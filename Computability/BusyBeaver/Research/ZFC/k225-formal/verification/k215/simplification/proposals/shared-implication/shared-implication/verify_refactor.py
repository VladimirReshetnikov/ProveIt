#!/usr/bin/env python3
"""Reproduce and check the proposed shared implicational proof refactoring.

Usage:
  python3 verify_refactor.py --repo /path/to/ProveIt --lean /path/to/lean \
      --output ./verification

The checkout must be at the pinned commit. Baseline bytes are read with git
show, so verification does not mutate or rely on checkout modifications.
The proposed bytes are never rewritten. The generated standalone projection
and compiler outputs are written only under --output.

Lean invocations are serialized under /tmp/proveit-k215-proof-build.lock,
using the repository's one-build-at-a-time convention. Full project endpoint
builds are explicitly outside this script's scope.
"""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

PIN = '2ca3a5c16f0876d2cab842056353c03a1ed2f5f0'
REQUIRED_LEAN_VERSION = '4.32.0'
LOCK = Path('/tmp/proveit-k215-proof-build.lock')
BASE = Path('Computability/BusyBeaver')
RESEARCH = BASE / 'Research/ZFC/k225-formal/rho8cd'
LEAN = BASE / 'Lean/BusyBeaver/ZFC'
RENDERER = RESEARCH / 'generate_domrho8_cd.py'
DERIVATION = RESEARCH / 'derivation_core.txt'
NAT_DERIVATION = RESEARCH / 'derivation.txt'
CORE = LEAN / 'DominatedImplication.lean'
LUK = LEAN / 'Lukasiewicz.lean'
GENERIC_NAMESPACE = 'SetTheory.BusyBeaver.ZFC.Lukasiewicz'
TARSKI_MARKER = 'namespace SetTheory.BusyBeaver.ZFC.Tarski\n'
EXPECTED_SHARED = [
    'SetTheory.BusyBeaver.ZFC.DominatedImplication.' + n
    for n in ('rho8_all', 'composition', 'lift_right', 'k', 'peirce', 's')
] + [GENERIC_NAMESPACE + '.' + n for n in ('k', 'peirce', 'composition', 's')]
EXPECTED_COUNTERMODEL = [
    'ProofSimplification.DiagonalCountermodel.' + n
    for n in ('mp', 'diagonal', 'unrestricted_fails', 'diagonal_does_not_suffice')
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_record(path: Path) -> dict:
    data = path.read_bytes()
    return {'path': str(path.resolve()), 'bytes': len(data), 'sha256': sha256(data)}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def git_bytes(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.PIPE)


def load_renderer(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot import renderer {path}')
    mod = importlib.util.module_from_spec(spec)
    # Keep imported-cache artifacts out of the proposed source directory.
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.dont_write_bytecode = previous
    return mod


def theorem_header(text: str, name: str) -> str:
    m = re.search(r'^theorem ' + re.escape(name) + r'\b([\s\S]*?):=', text, re.MULTILINE)
    require(m is not None, f'Missing public theorem {name}')
    return ' '.join(m.group(0).split())


def implicational_structure(text: str) -> str:
    m = re.search(r'^structure Implicational\b[\s\S]*?(?=\n\n)', text, re.MULTILINE)
    require(m is not None, 'Missing Implicational structure')
    return ' '.join(m.group(0).split())


def standalone_projection(core: str, luk: str) -> str:
    start = luk.index('namespace ' + GENERIC_NAMESPACE)
    end_marker = 'end ' + GENERIC_NAMESPACE
    end = luk.index(end_marker, start) + len(end_marker)
    text = core + '\n\n' + luk[start:end] + '\n\n'
    for name in ('k', 'peirce', 'composition', 's'):
        text += f'#print axioms {GENERIC_NAMESPACE}.{name}\n'
    return text


def axiom_reports(log: str) -> dict[str, list[str]]:
    reports = {}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", log):
        reports[m.group(1)] = []
    for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.DOTALL):
        reports[m.group(1)] = [s.strip() for s in m.group(2).split(',') if s.strip()]
    return reports


def run_logged(command: list[str], cwd: Path, log: Path) -> dict:
    start = utc_now()
    then = time.monotonic()
    with log.open('wb') as stream:
        proc = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    return {
        'command': command, 'cwd': str(cwd.resolve()), 'started_utc': start,
        'elapsed_seconds': round(time.monotonic() - then, 6),
        'returncode': proc.returncode, 'log': file_record(log),
    }


def compile_one(lean: Path, source: Path, output: Path, expected: list[str]) -> dict:
    olean = output / (source.stem + '.olean')
    log = output / (source.stem + '.lean.log')
    command = [str(lean), '-j1', '-M12288', '-o', str(olean), str(source)]
    result = run_logged(command, output, log)
    result['source'] = file_record(source)
    result['axiom_reports'] = axiom_reports(log.read_text(encoding='utf-8', errors='replace'))
    result['expected_axiom_reports'] = expected
    result['outputs'] = [file_record(p) for p in sorted(output.glob(source.stem + '.olean*')) if p.is_file()]
    result['outputs'] += [file_record(p) for p in sorted(output.glob(source.stem + '.ilean*')) if p.is_file()]
    result['all_expected_reports_present'] = all(n in result['axiom_reports'] for n in expected)
    result['all_expected_reports_axiom_free'] = all(result['axiom_reports'].get(n) == [] for n in expected)
    result['passed'] = (
        result['returncode'] == 0 and bool(result['outputs'])
        and result['all_expected_reports_present'] and result['all_expected_reports_axiom_free']
    )
    return result


def verify(args: argparse.Namespace, receipt: dict) -> None:
    repo = args.repo.resolve()
    proposal = args.proposal.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    receipt['repository'] = str(repo)
    head = git_bytes(repo, 'rev-parse', 'HEAD').decode().strip()
    receipt['observed_commit'] = head
    require(head == PIN, f'Expected checkout at {PIN}; found {head}')
    receipt['checks'].append({'check': 'pinned_commit', 'passed': True})

    baseline = {p: git_bytes(repo, 'show', f'{PIN}:{p.as_posix()}')
                for p in (RENDERER, DERIVATION, NAT_DERIVATION, CORE, LUK)}
    receipt['baseline_sources'] = [
        {'path': p.as_posix(), 'bytes': len(data), 'sha256': sha256(data)}
        for p, data in baseline.items()
    ]
    proposed = {p: (proposal / p).read_bytes() for p in (RENDERER, DERIVATION, CORE, LUK)}
    receipt['proposed_sources'] = [file_record(proposal / p) for p in proposed]
    b_luk = baseline[LUK].decode('utf-8')
    p_luk = proposed[LUK].decode('utf-8')
    p_core = proposed[CORE].decode('utf-8')

    # Signatures of all public generic basis theorems and their input structure.
    headers = {}
    for name in ('k', 'peirce', 'composition', 's'):
        before = theorem_header(b_luk, name)
        after = theorem_header(p_luk, name)
        require(before == after, f'Public theorem header changed: {name}')
        headers[name] = after
    require(implicational_structure(b_luk) == implicational_structure(p_luk),
            'Implicational structure changed')
    receipt['checks'].append({'check': 'public_basis_interfaces_identical', 'passed': True,
                              'normalized_headers': headers,
                              'normalized_structure': implicational_structure(p_luk)})
    b_tail = b_luk[b_luk.index(TARSKI_MARKER):].encode()
    p_tail = p_luk[p_luk.index(TARSKI_MARKER):].encode()
    require(b_tail == p_tail, 'Tarski bridge suffix changed')
    receipt['checks'].append({'check': 'tarski_suffix_byte_identical', 'passed': True,
                              'bytes': len(p_tail), 'sha256': sha256(p_tail)})

    with tempfile.TemporaryDirectory(prefix='k215-implication-reproduce-', dir=output) as td:
        temp = Path(td)
        old_renderer = temp / 'old_renderer.py'
        old_renderer.write_bytes(baseline[RENDERER])
        old_nat_derivation = temp / 'old_derivation.txt'
        old_nat_derivation.write_bytes(baseline[NAT_DERIVATION])
        new_mod = load_renderer(proposal / RENDERER, 'proposed_rho8_renderer')
        old_mod = load_renderer(old_renderer, 'baseline_rho8_renderer')
        rows, goals = new_mod.read(proposal / DERIVATION)
        regenerated = new_mod.render(rows, goals, 'core').encode('utf-8')
        generated_path = temp / 'DominatedImplication.lean'
        generated_path.write_bytes(regenerated)
        require(regenerated == proposed[CORE], 'Core is not byte-for-byte regenerated from its producer')
        receipt['checks'].append({'check': 'core_regeneration_byte_identical', 'passed': True,
                                  'sha256': sha256(regenerated), 'bytes': len(regenerated)})
        for mode in ('lean', 'rocq'):
            before = old_mod.render(*old_mod.read(old_nat_derivation), mode).encode('utf-8')
            after = new_mod.render(*new_mod.read(old_nat_derivation), mode).encode('utf-8')
            require(before == after, f'Old 52-step {mode} rendering changed')
            receipt['checks'].append({'check': f'old_nat_{mode}_rendering_byte_identical',
                                      'passed': True, 'sha256': sha256(after), 'bytes': len(after)})

    projection = standalone_projection(p_core, p_luk).encode('utf-8')
    checked_in_projection = proposal / 'SharedImplicationCore.lean'
    require(checked_in_projection.read_bytes() == projection,
            'Standalone proof does not exactly project the proposed source files')
    standalone = output / 'SharedImplicationCore.lean'
    standalone.write_bytes(projection)
    receipt['checks'].append({'check': 'standalone_exact_projection', 'passed': True,
                              'source': file_record(standalone)})
    countermodel = output / 'DiagonalCountermodel.lean'
    countermodel.write_bytes(args.countermodel.resolve().read_bytes())
    receipt['countermodel_source'] = file_record(countermodel)

    if args.check_only:
        receipt['validation_level'] = 'source_checks_only'
        receipt['status'] = 'PASS_SOURCE_CHECKS_ONLY'
        return
    require(args.lean is not None, '--lean is required unless --check-only is used')
    lean = args.lean.resolve()
    require(lean.is_file(), f'Lean executable missing: {lean}')
    receipt['lean_executable'] = file_record(lean)
    receipt['build_lock'] = str(LOCK)
    try:
        import fcntl
    except ImportError as exc:
        raise RuntimeError('This verifier needs POSIX fcntl for the required serial build lock') from exc
    print(f'Waiting for serial compiler lock: {LOCK}', flush=True)
    with LOCK.open('a+b') as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        version_result = run_logged([str(lean), '--version'], output, output / 'lean-version.log')
        receipt['lean_version'] = version_result
        version_text = (output / 'lean-version.log').read_text(encoding='utf-8', errors='replace').strip()
        receipt['lean_version']['text'] = version_text
        require(version_result['returncode'] == 0, 'lean --version failed')
        require(re.search(r'\bversion ' + re.escape(REQUIRED_LEAN_VERSION) + r'(?:,|\s|\))', version_text) is not None,
                f'Expected Lean {REQUIRED_LEAN_VERSION}; found {version_text}')
        for source, expected in ((standalone, EXPECTED_SHARED), (countermodel, EXPECTED_COUNTERMODEL)):
            print(f'Compiling {source.name}', flush=True)
            result = compile_one(lean, source, output, expected)
            receipt['compilations'].append(result)
            require(result['passed'], f'Kernel check or axiom audit failed: {source.name}; inspect {result["log"]["path"]}')
        fcntl.flock(lock.fileno(), fcntl.LOCK_UN)
    receipt['validation_level'] = 'changed_mathematical_core_and_adapters_plus_countermodel'
    receipt['status'] = 'PASS_STANDALONE_KERNEL_CHECKS'


def main() -> int:
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--lean', type=Path)
    ap.add_argument('--proposal', type=Path, default=here / 'refactor')
    ap.add_argument('--countermodel', type=Path, default=here / 'DiagonalCountermodel.lean')
    ap.add_argument('--output', type=Path, default=here / 'verification')
    ap.add_argument('--check-only', action='store_true', help='Run only source checks; do not invoke Lean')
    args = ap.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    receipt = {
        'schema': 'proveit-k215-shared-implication-verification-v1',
        'pinned_commit': PIN, 'required_lean_version': REQUIRED_LEAN_VERSION,
        'started_utc': utc_now(), 'status': 'IN_PROGRESS', 'checks': [], 'compilations': [],
        'verifier': file_record(Path(__file__).resolve()),
        'scope': 'Exact changed mathematical core and generic adapters; no full K215 endpoint build.',
        'full_endpoint_rebuilt': False,
    }
    exitcode = 0
    try:
        verify(args, receipt)
    except Exception as exc:
        receipt['status'] = 'FAIL'
        receipt['error'] = {'type': type(exc).__name__, 'message': str(exc)}
        print(f'{type(exc).__name__}: {exc}', file=sys.stderr)
        exitcode = 1
    finally:
        receipt['finished_utc'] = utc_now()
        destination = args.output / 'verification.json'
        destination.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
        print(f'{receipt["status"]}: {destination}', flush=True)
    return exitcode


if __name__ == '__main__':
    raise SystemExit(main())
