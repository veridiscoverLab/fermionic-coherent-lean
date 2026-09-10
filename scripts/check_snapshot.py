#!/usr/bin/env python3
"""Check archived verification integrity. Does not run Lean or replay proofs."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
REV = "8a178386ffc0f5fef0b77738bb5449d50efeea95"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SUITES = (
    ("evidence", "20260909T234218Z", "verify_remote.py", "Fermionic", 20, 399, 309),
    ("rank_evidence", "20260910T013918Z", "verify_rank_remote.py", "FermionicRank", 33, 384, 257),
    ("rank_geometry_evidence", "20260910T012634Z", "verify_rank_geometry_remote.py",
     "FermionicRankGeometry", 12, 190, 150),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_path(relative):
    p = PurePosixPath(relative)
    require(not p.is_absolute() and ".." not in p.parts, f"Invalid path: {relative}")
    path = ROOT / relative
    require(path.is_file() and not path.is_symlink(), f"Missing regular file: {relative}")
    return path


def import_closure(aggregate):
    """Read the simple project import lines in the checksum-pinned sources."""
    pending, visited = [aggregate + ".lean"], set()
    while pending:
        relative = pending.pop()
        if relative in visited:
            continue
        visited.add(relative)
        code = checked_path(relative).read_text()
        for module in re.findall(r"^import\s+(Fermionic(?:\.\w+)+)\s*$", code, re.M):
            pending.append(module.replace(".", "/") + ".lean")
    visited.remove(aggregate + ".lean")
    return visited


def main():
    evidence_files = {}
    for line in (ROOT / "recorded-evidence.sha256").read_text().splitlines():
        checksum, relative = line.split(maxsplit=1)
        relative = relative.strip()
        require(re.fullmatch(r"[0-9a-f]{64}", checksum), f"Invalid digest: {relative}")
        require(relative not in evidence_files, f"Repeated evidence path: {relative}")
        evidence_files[relative] = checksum
        require(digest(checked_path(relative)) == checksum, f"Changed evidence: {relative}")
    observed_evidence = {
        p.relative_to(ROOT).as_posix()
        for folder, *_ in SUITES
        for p in (ROOT / folder).rglob("*") if p.is_file()
    }
    require(set(evidence_files) == observed_evidence, "Evidence file inventory differs")

    lock = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies = {p["name"]: p["rev"] for p in lock["packages"]}
    require(dependencies["mathlib"] == REV, "Unexpected mathlib pin")
    require((ROOT / "lean-toolchain").read_text().strip() ==
            "leanprover/lean4:v4.29.0", "Unexpected Lean pin")
    shared_sources, shared_declarations, summaries = {}, {}, []
    versions = set()

    for folder, run_id, runner, aggregate, modules, declarations, theorems in SUITES:
        result = json.loads((ROOT / folder / "result.json").read_text())
        require(result["utc_started"] == run_id, f"Wrong recorded run: {folder}")
        require(result["utc_completed"] >= run_id, f"Invalid completion time: {folder}")
        require(result["mathlib_revision"] == REV, f"Wrong mathlib: {folder}")
        require(result["dependency_revisions"] == dependencies, f"Dependency mismatch: {folder}")
        require("version 4.29.0," in result["lean"], f"Wrong Lean: {folder}")
        versions.add(result["lean"])
        for field in ("source_hygiene", "clean_compile", "fresh_kernel_replay_including_imports"):
            require(result[field] == "PASS", f"Recorded failure: {folder}/{field}")
        require(result["full_paper_verified"] is False, f"Incorrect whole-paper scope: {folder}")
        if folder != "evidence":
            require(result["physical_gaussian_rank_four_verified"] is False,
                    f"Incorrect rank-four scope: {folder}")
        else:
            for field in ("exterior_husimi_haar_core_verified", "exterior_slater_orbit_core_verified",
                          "exterior_positive_moments_and_entropy_minima_verified"):
                require(result[field] is True, f"Missing exterior scope: {field}")
            require(result["explicit_beta_gamma_constants_verified"] is False,
                    "Incorrect explicit-constant scope")
        if folder == "rank_geometry_evidence":
            require(result["original_target_rank_at_least_two_verified"] is True,
                    "Missing original-target lower bound")

        for relative, checksum in result["source_sha256"].items():
            require(digest(checked_path(relative)) == checksum, f"Source mismatch: {relative}")
            require(shared_sources.get(relative, checksum) == checksum,
                    f"Conflicting shared source: {relative}")
            shared_sources[relative] = checksum
        module_paths = {p for p in result["source_sha256"] if p.startswith("Fermionic/")}
        require(len(module_paths) == modules, f"Module count mismatch: {folder}")
        require(aggregate + ".lean" in result["source_sha256"], f"Missing aggregate: {folder}")
        require(import_closure(aggregate) == module_paths, f"Aggregate coverage mismatch: {folder}")

        executed = runner.removesuffix(".py") + "_executed.py"
        for path in (ROOT / runner, ROOT / folder / executed):
            require(digest(path) == result["verifier_sha256"], f"Runner mismatch: {path.name}")
        names = {d["name"] for d in result["declarations"]}
        require(len(names) == len(result["declarations"]) == declarations,
                f"Declaration inventory mismatch: {folder}")
        counted = sum(d["kind"] in ("theorem", "lemma") for d in result["declarations"])
        require(counted == result["theorem_count"] == theorems, f"Theorem count mismatch: {folder}")
        require(set(result["core_roots"]) <= names, f"Missing target-facing root: {folder}")
        for d in result["declarations"]:
            name = d["name"]
            require(d["source"] in module_paths, f"Unverified declaration source: {name}")
            require(set(result["axioms"][name]) <= ALLOWED_AXIOMS, f"Unexpected axiom: {name}")
            require(shared_declarations.get(name, d) == d, f"Conflicting declaration: {name}")
            shared_declarations[name] = d
        for log in ("declaration-types-and-axioms.log", "kernel-fresh-replay.log"):
            require((ROOT / folder / "logs" / log).stat().st_size > 0, f"Missing log: {folder}/{log}")
        summaries.append({"suite": folder, "recorded_run": run_id, "modules": modules,
                          "declarations": declarations, "theorems": theorems})

    require(len(versions) == 1, "Recorded Lean builds differ")
    expected_lean = {p for p in shared_sources if p.endswith(".lean")}
    actual_lean = {p.relative_to(ROOT).as_posix() for p in (ROOT / "Fermionic").rglob("*.lean")}
    actual_lean |= {p.name for p in ROOT.glob("*.lean")}
    require(actual_lean == expected_lean, "Project contains missing or unverified Lean source")
    require(len(shared_sources) == 58 and len(shared_declarations) == 752,
            "Unexpected union inventory")
    module_count = sum(p.startswith("Fermionic/") for p in shared_sources)
    theorem_count = sum(d["kind"] in ("theorem", "lemma") for d in shared_declarations.values())
    require(module_count == 52 and theorem_count == 547, "Unexpected union counts")
    print(json.dumps({"snapshot_integrity": "PASS", "fresh_replay_performed_by_this_check": False,
                      "recorded_suites": summaries, "union_modules": module_count,
                      "union_declarations": len(shared_declarations), "union_theorems": theorem_count,
                      "full_paper_verified": False, "physical_gaussian_rank_four_verified": False},
                     indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Snapshot integrity FAILED: {error}", file=sys.stderr)
        sys.exit(1)
