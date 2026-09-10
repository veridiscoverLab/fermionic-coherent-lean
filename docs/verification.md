# Reproducing the verification

## What was verified

The repository preserves the proof sources, three aggregate imports, dependency
lock files, verification runners, and evidence from these successful runs:

| Suite | UTC run ID | Declarations | Theorems | Aggregate |
| --- | --- | ---: | ---: | --- |
| Exterior powers and entropy | `20260909T234218Z` | 399 | 309 | `Fermionic.lean` |
| Gaussian-rank foundations and certificate | `20260910T013918Z` | 384 | 257 | `FermionicRank.lean` |
| Vacuum-chart rigidity | `20260910T012634Z` | 190 | 150 | `FermionicRankGeometry.lean` |

The source and runner bytes are unchanged from these runs. This repository
assembly does not constitute a fourth clean build or kernel replay. The two
rank suites together cover 34 modules, 398 declarations, and 271 theorems;
their overlap is counted once. Counts describe coverage, not the strength of
the mathematical conclusions.

The default Lake target is the exterior suite. The rank aggregates have their
own verification runners; building the default target alone does not verify
the rank suites.

## Execution environment

All recorded Lean and Lake execution took place through SSH on `cab17`, whose
hostname is `CAB-Lab-Server-8`. The supplied runners intentionally enforce this
host and require their checkout to be below `/home/dzheng/remote_builds/`.
They use:

```text
Lean:    leanprover/lean4:v4.29.0
mathlib: 8a178386ffc0f5fef0b77738bb5449d50efeea95
Lean bin directory:
  /home/dzheng/.elan/toolchains/leanprover--lean4---v4.29.0/bin
```

The complete dependency revisions are pinned in `lake-manifest.json` and
recorded in each `result.json`. Dependency sources and build caches are not
vendored. The existing CAB package cache is read-only; the runners check each
package's Git revision and tracked-file cleanliness before compiling.

## Set up a separate CAB checkout

Copy or clone this repository to a new directory on CAB17, for example
`/home/dzheng/remote_builds/fermionic-coherent-lean`. Exclude `.git` if using a
source-only transfer, and never transfer local build caches. Then run through
SSH:

```sh
ssh cab17
cd /home/dzheng/remote_builds/fermionic-coherent-lean
mkdir -p .lake
ln -s /home/dzheng/remote_builds/fermionic_coherent_formal_20260909/.lake/packages .lake/packages
python3 scripts/check_snapshot.py
python3 verify_remote.py
python3 verify_rank_remote.py
python3 verify_rank_geometry_remote.py
```

Create the symlink only if `.lake/packages` does not already exist; retain a
correct existing link. The cache and toolchain must exist on the server.
Changing hosts or toolchain locations requires adapting the runner's explicit
environment guards and generating new evidence; the archived runs certify
the original runners. Do not silently remove those guards or execute locally.

Each verification runner copies its selected source files into a new empty
project-build directory, compiles them with warnings treated as errors,
prints every selected declaration's full type and transitive axioms, and runs:

```text
lake env leanchecker --fresh --verbose <aggregate>
```

The successful result is written only after all stages pass. The three runners
write separate timestamped directories and `LATEST_*` pointers. They do not
overwrite the archived evidence directories tracked in this repository.

## Reading the evidence

Each of `evidence/`, `rank_evidence/`, and `rank_geometry_evidence/` contains:

- `result.json`: versions, source and runner hashes, declaration inventory,
  transitive axioms, verification status, and mathematical scope.
- `Audit.lean`: explicit declaration-type and axiom queries.
- `source_sha256.txt`: checksums relative to the repository root.
- `verify_*_executed.py`: the runner used for that recorded run.
- `logs/`: strict compilation, dependency checks, type/axiom audit, and fresh
  kernel-replay output.

`recorded-evidence.sha256` records checksums for all archived evidence files.
`scripts/check_snapshot.py` checks that the current source, configuration,
runners, and evidence agree with the archived successful snapshots. It also
checks selected scope flags and shared-source consistency. It does **not**
compile Lean or establish a new mathematical theorem.

## Trust boundary

The proof scripts contain no `sorry`, `admit`, added mathematical axiom, or
`native_decide`. Finite certificate leaves use ordinary kernel `decide`;
parameter identities use kernel-checked algebraic proofs.

All selected declarations depend only on the disclosed logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. Fresh replay reconstructs all
replayable safe, non-partial constants in the imported environment with the
same Lean kernel, starting from an empty environment; axioms remain axioms.
It is not a second independent implementation of the kernel, and third-party
dependency source files were not all recompiled from scratch in each run.

Kernel acceptance certifies the formal statements relative to these
foundations. The mathematical scope is stated in [theorems.md](theorems.md)
and [the rank proof notes](gaussian-rank-proof.md); neither incomplete geometric
bridges nor historical priority claims are supplied by the checker.
