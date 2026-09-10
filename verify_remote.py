#!/usr/bin/env python3
"""CAB-only clean compilation, declaration audit and full kernel replay.

Successful execution certifies the selected Lean modules, including the full
exterior Husimi roots. It does not certify the entire paper or eight-mode rank.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import socket
import subprocess
import time

ROOT = Path(__file__).resolve().parent
VERIFIER_BYTES = Path(__file__).read_bytes()
VERIFIER_SHA256 = hashlib.sha256(VERIFIER_BYTES).hexdigest()
if not str(ROOT).startswith('/home/dzheng/remote_builds/'):
    raise SystemExit('Execution is permitted only in the CAB remote build directory.')
if socket.gethostname() != 'CAB-Lab-Server-8':
    raise SystemExit('This run is pinned to cab17 / CAB-Lab-Server-8.')
BIN = '/home/dzheng/.elan/toolchains/leanprover--lean4---v4.29.0/bin'
ENV = dict(os.environ, PATH=BIN + ':' + os.environ.get('PATH', ''))
REV = '8a178386ffc0f5fef0b77738bb5449d50efeea95'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MODULES = ['Fock', 'Spinor', 'CommonJensen', 'DensityRigidity', 'FourMode',
           'ExteriorUnitary', 'HaarConditioning', 'ExteriorDifferential',
           'OccupationMixture', 'ConditionalSector', 'OccupancyOrbit',
           'OccupationConvexOrder', 'SlaterOrbit', 'SlaterOneParticle',
           'SlaterClosure', 'ExteriorHusimi', 'HusimiScale', 'HusimiInduction',
           'SlaterMeasure', 'ExteriorEntropy']
CORE_ROOTS = ['Fermionic.HusimiInduction.' + s for s in
              ['exterior_husimi_convex_order', 'exterior_husimi_equality_iff',
               'exterior_husimi_convex_order_any_slater']]
CORE_ROOTS += ['Fermionic.SlaterMeasure.' + s for s in
               ['orbitMeasure_invariant', 'orbitMeasure_reference_independent',
                'orbit_husimi_convex_order', 'orbit_husimi_equality_iff']]
CORE_ROOTS += ['Fermionic.ExteriorEntropy.' + s for s in
               ['sectorDimension_eq_choose', 'normalizedMoment_one',
                'wehrl_minimum', 'wehrl_eq_iff_slater',
                'renyiWehrl_minimum', 'renyiWehrl_eq_iff_slater']]
STAMP = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
RUN = ROOT / 'verification_runs' / STAMP
CLEAN = RUN / 'clean'
LOGS = RUN / 'logs'
LOGS.mkdir(parents=True, exist_ok=False)
(RUN / 'verify_remote_executed.py').write_bytes(VERIFIER_BYTES)
(CLEAN / 'Fermionic').mkdir(parents=True)
(CLEAN / '.lake/build/lib/lean/Fermionic').mkdir(parents=True)
(CLEAN / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(),
                                     target_is_directory=True)


def run(args, cwd, name):
    target = LOGS / name
    with target.open('w') as output:
        proc = subprocess.run(args, cwd=cwd, env=ENV, stdout=output,
                              stderr=subprocess.STDOUT)
    if proc.returncode:
        raise RuntimeError(f'{args!r}: exit {proc.returncode}; see {target}')
    return target.read_text()


def uncomment(source):
    """Remove nested comments, keeping string contents and newlines intact."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        if depth:
            if source[i:i+2] == '/-':
                depth += 1
                i += 2
            elif source[i:i+2] == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(source[i])
            if source[i] == '\\' and i + 1 < len(source):
                out.append(source[i+1])
                i += 2
                continue
            if source[i] == '"':
                quoted = False
            i += 1
        elif source[i:i+2] == '/-':
            depth = 1
            out.append(' ')
            i += 2
        elif source[i:i+2] == '--':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            quoted = source[i] == '"'
            i += 1
    if depth or quoted:
        raise RuntimeError('Unterminated comment or string')
    return ''.join(out)


manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
if mathlib['rev'] != REV:
    raise RuntimeError('Unexpected mathlib revision in manifest')
actual_rev = run(['git', 'rev-parse', 'HEAD'], ROOT / '.lake/packages/mathlib',
                 'mathlib-revision.log').strip()
if actual_rev != REV:
    raise RuntimeError('The linked mathlib checkout differs from its pinned revision')
dependencies = {}
for package in manifest['packages']:
    location = ROOT / '.lake/packages' / package['name']
    observed = run(['git', 'rev-parse', 'HEAD'], location,
                   'dependency-' + package['name'] + '.log').strip()
    dirty = run(['git', 'status', '--porcelain', '--untracked-files=no'], location,
                'dependency-status-' + package['name'] + '.log').strip()
    if observed != package['rev'] or dirty:
        raise RuntimeError('Dependency checkout is not the clean pinned source: ' + package['name'])
    dependencies[package['name']] = observed

files = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Fermionic.lean']
files += ['Fermionic/' + m + '.lean' for m in MODULES]
hashes, declarations, theorem_count = {}, [], 0
for name in files:
    payload = (ROOT / name).read_bytes()
    (CLEAN / name).write_bytes(payload)
    hashes[name] = hashlib.sha256(payload).hexdigest()
    if not name.endswith('.lean'):
        continue
    code = uncomment(payload.decode())
    forbidden = re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|partial|implemented_by|'
                          r'run_tac|run_elab|elab|macro|opaque)\b|#eval|skipKernelTC', code)
    if forbidden:
        raise RuntimeError(f'Forbidden proof mechanism in {name}: {forbidden.group()}')
    if name == 'Fermionic.lean':
        for line in code.splitlines():
            if line.strip() and line.strip() not in {'import Fermionic.' + m for m in MODULES}:
                raise RuntimeError('The aggregate may only import selected modules: ' + line)
        continue
    if re.search(r'\b(structure|class|inductive|initialize)\b', code):
        raise RuntimeError('Extend and audit the declaration inventory before accepting ' + name)
    namespaces = re.findall(r'^namespace\s+(\S+)', code, re.M)
    if len(namespaces) != 1 or not namespaces[0].startswith('Fermionic.'):
        raise RuntimeError('Unsupported namespace layout in ' + name)
    namespace = namespaces[0]
    pattern = (r'^(?:@\[[^\]\n]*\]\s*)?(?:noncomputable\s+)?'
               r'(theorem|lemma|def|abbrev|instance)\s+([\w.]+)')
    named = re.findall(pattern, code, re.M)
    # Fail closed if declaration syntax has escaped this restricted inventory.
    if len(named) != len(re.findall(r'\b(?:theorem|lemma|def|abbrev|instance)\s+', code)):
        raise RuntimeError('Declaration inventory is incomplete in ' + name)
    for kind, short_name in named:
        declarations.append({'name': namespace + '.' + short_name,
                             'kind': kind, 'source': name})
        theorem_count += kind in ('theorem', 'lemma')

if not set(CORE_ROOTS).issubset({d['name'] for d in declarations}):
    raise RuntimeError('A required target-facing root is absent from the source inventory')

version = run(['lake', 'env', 'lean', '--version'], CLEAN, 'lean-version.log').strip()
if 'version 4.29.0,' not in version:
    raise RuntimeError('Unexpected Lean version: ' + version)

# Each project source is compiled from scratch. Package binaries are only read.
for module in MODULES + ['']:
    stem = 'Fermionic/' + module if module else 'Fermionic'
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '-o',
         '.lake/build/lib/lean/' + stem + '.olean', stem + '.lean'],
        CLEAN, 'compile-' + (module or 'aggregate') + '.log')

audit = ['import Fermionic', 'set_option pp.universes true',
         'set_option pp.explicit true', 'set_option pp.fullNames true']
for item in declarations:
    audit += ['#check @' + item['name']]
audit += ['set_option pp.universes false']
for item in declarations:
    audit += ['#print axioms ' + item['name']]
(CLEAN / 'Audit.lean').write_text('\n'.join(audit) + '\n')
audit_text = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'],
                 CLEAN, 'declaration-types-and-axioms.log')
axioms = {}
for name, deps in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text):
    axioms[name] = [x.strip() for x in deps.split(',') if x.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", audit_text):
    axioms[name] = []
for item in declarations:
    if item['name'] not in axioms:
        raise RuntimeError('Missing axiom report: ' + item['name'])
    extra = set(axioms[item['name']]) - ALLOWED_AXIOMS
    if extra:
        raise RuntimeError(f'Undisclosed axioms: {item["name"]}: {extra}')

print('Clean compilation and all declaration audits passed; starting fresh replay.', flush=True)
run(['lake', 'env', 'leanchecker', '--fresh', '--verbose', 'Fermionic'],
    CLEAN, 'kernel-fresh-replay.log')

result = {
    'host': socket.gethostname(), 'ssh_alias': 'cab17', 'run_directory': str(RUN),
    'utc_started': STAMP, 'utc_completed': time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()),
    'lean': version, 'mathlib_revision': REV, 'source_sha256': hashes,
    'dependency_revisions': dependencies,
    'verifier_sha256': VERIFIER_SHA256,
    'declarations': declarations, 'theorem_count': theorem_count,
    'axioms': axioms, 'source_hygiene': 'PASS', 'clean_compile': 'PASS',
    'fresh_kernel_replay_including_imports': 'PASS',
    'kernel_replay_scope': ('Same Lean kernel, all replayable safe non-partial constants in the '
                            'imported environment replayed from empty; axioms remain axioms.'),
    'full_paper_verified': False,
    'exterior_husimi_haar_core_verified': True,
    'exterior_slater_orbit_core_verified': True,
    'exterior_positive_moments_and_entropy_minima_verified': True,
    'explicit_beta_gamma_constants_verified': False,
    'core_roots': CORE_ROOTS,
    'scope': ('Full exterior Husimi convex order and strict equality on the original U(n) Haar '
              'measurement and original Slater projector-orbit measure, with all physical '
              'representation and conditional-state bridges. All positive real power moments, '
              'Wehrl and Renyi-Wehrl minima and strict equality are included. Explicit '
              'Beta/Gamma coherent constants are not included. '
              'Half-spin, eight-mode physical Gaussian rank and full-paper verification remain open.')
}
(RUN / 'result.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
(ROOT / 'LATEST_RUN.txt').write_text(str(RUN) + '\n')
print(json.dumps({'run': str(RUN), 'declarations': len(declarations),
                  'theorems': theorem_count, 'verification': 'PASS',
                  'exterior_husimi_haar_core_verified': True,
                  'full_paper_verified': False}, ensure_ascii=False), flush=True)
