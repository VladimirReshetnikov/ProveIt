"""Recover intake157 source50 offline and replay its substantive finite suites.

Default: recover all67 delivered files and run10 functional checks, including
both delivered compressed search partitions and the exact baseline bootstrap.
Only the named degree-one transport line-ending/hash provenance loop is skipped
in memory. No delivered file is patched. --extended additionally repeats the
complete degree-one search and compares its full journal; it does not rerun the
600-second degree-two search. --prepare-only recovers without executing suites.
No network, Lean, Coq or compiler is used. Keep Python assertions enabled.
"""
from __future__ import annotations

import argparse
import ast
import gzip
import io
import itertools
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
import time
from zipfile import ZipFile

ARRIVAL = '85633fd2f57b5dca16f87667699134d1b500ebc0'
ARCHIVE = 'docs/incoming/zfc_sparse_certificates.zip'
WRAPPER = 'zfc_sparse_certificates'
HOST = Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')
ARCHIVE_ONLY = {'README.txt', 'machine_experiments/research_notes.tex',
                'report.pdf', 'report.tex', 'zfc_sparse_certificates.tex'}
# Exact delivery-to-host names from intake157 placement-map.json. This is a
# recovery map, not a checksum manifest. The62 hosted bytes are compared directly
# with their committed delivery counterparts before use.
PLACED_NAMES = {
    "ATTRIBUTION.txt": "data/50-terms-ATTRIBUTION.txt",
    "MANIFEST.json": "data/50-terms-MANIFEST.json",
    "Makefile": "code/50-terms-Makefile",
    "TERM254.txt": "data/50-terms-TERM254.txt",
    "code/audit_canonical.py": "code/50-terms-code-audit_canonical.py",
    "code/canonical254.py": "code/50-terms-code-canonical254.py",
    "code/check_proof_code_size.py": "code/50-terms-code-check_proof_code_size.py",
    "code/check_term254.py": "code/50-terms-code-check_term254.py",
    "code/extract_specs.py": "code/50-terms-code-extract_specs.py",
    "code/replay_all.py": "code/50-terms-code-replay_all.py",
    "code/reproduce.py": "code/50-terms-code-reproduce.py",
    "code/schema_metrics.py": "code/50-terms-code-schema_metrics.py",
    "code/symbolic254.py": "code/50-terms-code-symbolic254.py",
    "code/term254.py": "code/50-terms-code-term254.py",
    "data/canonical_audit_results.json": "data/50-terms-data-canonical_audit_results.json",
    "data/example_certificate.json": "data/50-terms-data-example_certificate.json",
    "data/example_mp_certificate.json": "data/50-terms-data-example_mp_certificate.json",
    "data/example_term_bundle_control.json": "data/50-terms-data-example_term_bundle_control.json",
    "data/package_replay_results.json": "data/50-terms-data-package_replay_results.json",
    "data/proof_code_size_results.json": "data/50-terms-data-proof_code_size_results.json",
    "data/report_qa.json": "data/50-terms-data-report_qa.json",
    "data/requested_commits.json": "data/50-terms-data-requested_commits.json",
    "data/schema_metrics.json": "data/50-terms-data-schema_metrics.json",
    "data/source_provenance.json": "data/50-terms-data-source_provenance.json",
    "data/sparse_certificate_results.json": "data/50-terms-data-sparse_certificate_results.json",
    "data/spec254.json": "data/50-terms-data-spec254.json",
    "data/term_certificate_results.json": "data/50-terms-data-term_certificate_results.json",
    "machine_experiments/README.txt": "data/50-terms-machine_experiments-README.txt",
    "machine_experiments/continuation_obstruction.json": "data/50-terms-machine_experiments-continuation_obstruction.json",
    "machine_experiments/continuation_obstruction.py": "code/50-terms-machine_experiments-continuation_obstruction.py",
    "machine_experiments/entry_degree1.json": "data/50-terms-machine_experiments-entry_degree1.json",
    "machine_experiments/entry_degree1.jsonl.gz": "data/50-terms-machine_experiments-entry_degree1.jsonl.gz",
    "machine_experiments/entry_degree1_partition_audit.json": "data/50-terms-machine_experiments-entry_degree1_partition_audit.json",
    "machine_experiments/entry_degree2.json": "data/50-terms-machine_experiments-entry_degree2.json",
    "machine_experiments/entry_degree2.jsonl.gz": "data/50-terms-machine_experiments-entry_degree2.jsonl.gz",
    "machine_experiments/entry_degree2_partition_audit.json": "data/50-terms-machine_experiments-entry_degree2_partition_audit.json",
    "machine_experiments/entry_resynthesis.py": "code/50-terms-machine_experiments-entry_resynthesis.py",
    "machine_experiments/integration_review.json": "data/50-terms-machine_experiments-integration_review.json",
    "machine_experiments/manifest.json": "data/50-terms-machine_experiments-manifest.json",
    "machine_experiments/reference_manifest.json": "data/50-terms-machine_experiments-reference_manifest.json",
    "machine_experiments/replay_entry_partition.py": "code/50-terms-machine_experiments-replay_entry_partition.py",
    "machine_experiments/transport_normalization.json": "data/50-terms-machine_experiments-transport_normalization.json",
    "reference/proveit/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryPerm252.lean": "code/50-terms-reference-proveit-lean-BinaryPerm252.lean",
    "reference/proveit/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean": "code/50-terms-reference-proveit-lean-Code254.lean",
    "reference/proveit/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Proof.lean": "code/50-terms-reference-proveit-lean-Code254Proof.lean",
    "reference/proveit/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254ProofCompiler.lean": "code/50-terms-reference-proveit-lean-Code254ProofCompiler.lean",
    "reference/proveit/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFCBoundPerm252.lean": "code/50-terms-reference-proveit-lean-ZFCBoundPerm252.lean",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/binary_perm252.md": "50-terms-reference-proveit-research-binary_perm252.md",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md": "50-terms-reference-proveit-research-candidate-permutation252-README.md",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/renumbering.json": "data/50-terms-reference-proveit-research-candidate-permutation252-renumbering.json",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252.tm": "data/50-terms-reference-proveit-research-candidate-permutation252-zfc_permutation252.tm",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm": "data/50-terms-reference-proveit-research-candidate-permutation252-zfc_permutation252_old.tm",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/candidate252_independent_audit.py": "code/50-terms-reference-proveit-research-candidate252_independent_audit.py",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/code254_arithmetic_checker.md": "50-terms-reference-proveit-research-code254_arithmetic_checker.md",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/constructible_choice_review.md": "50-terms-reference-proveit-research-constructible_choice_review.md",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/pa_internalization.md": "50-terms-reference-proveit-research-pa_internalization.md",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/permutation252_continuations.py": "code/50-terms-reference-proveit-research-permutation252_continuations.py",
    "reference/proveit/Computability/BusyBeaver/Research/ZFC/results/binary-perm252-integration-verification.json": "data/50-terms-reference-proveit-research-results-binary-perm252-integration-verification.json",
    "reference/proveit/LICENSE": "50-terms-reference-proveit-LICENSE",
    "reference/proveit/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py": "code/50-terms-reference-proveit-host-code-27-variant-experiments-machine_search-grammar_search-strict_affine.py",
    "reference/proveit/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v": "code/50-terms-reference-proveit-upstream-ZF-m254-coq-tm-Prog254.v",
    "reference/upstream/ZF/README.md": "50-terms-reference-upstream-ZF-README.md"
}


def recover(repo: Path, work: Path) -> tuple[Path, dict]:
    raw = subprocess.check_output(['git', 'show', f'{ARRIVAL}:{ARCHIVE}'], cwd=repo)
    package = work / WRAPPER
    package.mkdir()
    rows, seen = [], set()
    with ZipFile(io.BytesIO(raw)) as zipped:
        for member in zipped.infolist():
            relative = PurePosixPath(member.filename)
            if ('\\' in member.filename or relative.is_absolute()
                    or '..' in relative.parts or not relative.parts
                    or relative.parts[0] != WRAPPER):
                raise ValueError('Unexpected or unsafe archive path.')
            if ((member.external_attr >> 16) & 0o170000) == 0o120000:
                raise ValueError('Archive symlink rejected.')
            if member.is_dir():
                continue
            name = PurePosixPath(*relative.parts[1:]).as_posix()
            if name in seen or name not in PLACED_NAMES.keys() | ARCHIVE_ONLY:
                raise ValueError('Duplicate or unexpected archive member: ' + name)
            seen.add(name)
            delivered = zipped.read(member)
            target = HOST / PLACED_NAMES[name] if name in PLACED_NAMES else None
            if target is not None:
                hosted = repo / target
                if not hosted.is_file():
                    raise ValueError('Missing hosted ancillary: ' + str(target))
                data = hosted.read_bytes()
                if data != delivered:
                    raise ValueError('Hosted ancillary differs from delivery: ' + str(target))
                origin = 'unchanged hosted ancillary; directly compared to arrival bytes'
            else:
                data, origin = delivered, 'committed arrival archive only'
            destination = package / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            rows.append({'local_source': 50, 'delivered': name,
                         'recovered': str(destination),
                         'target': str(target) if target is not None else None,
                         'bytes': len(data), 'recovery': origin})
    if seen != PLACED_NAMES.keys() | ARCHIVE_ONLY or len(seen) != 67 or len(PLACED_NAMES) != 62:
        raise ValueError('Source50 delivery inventory differs.')
    mapping = {'batch': 157, 'local_source': 50, 'arrival': ARRIVAL,
               'archive': ARCHIVE, 'files': sorted(rows, key=lambda row: row['delivered']),
               'counts': {'files': 67, 'hosted': 62, 'archive_only': 5},
               'scope': 'Offline exact filename recovery from62 unchanged hosted ancillaries and5 archive-only files. Direct delivery byte comparison is a recovery identity; no bulk checksum or line-ending manifest is executed.'}
    (work / 'recovered-paths.json').write_text(json.dumps(mapping, indent=2) + '\n')
    return package, mapping


def functional_worker(package: Path, output: Path, replay: Path, adapter: Path) -> None:
    """Omit only the named line-ending provenance input/loop; retain all tests."""
    script = package / 'code/replay_all.py'
    tree = ast.parse(script.read_text(), filename=str(script))
    class Adapter(ast.NodeTransformer):
        def __init__(self):
            self.edits, self.statuses, self.temporary_calls = [], 0, 0
        def visit_Assign(self, node):
            if (len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                    and node.targets[0].id == 'norm'
                    and 'transport_normalization.json' in ast.unparse(node.value)):
                self.edits.append({'line': node.lineno, 'skip': 'degree-one line-ending provenance input'})
                return ast.copy_location(ast.Pass(), node)
            return self.generic_visit(node)
        def visit_For(self, node):
            if ast.unparse(node.iter) == "norm['files'].items()":
                self.edits.append({'line': node.lineno, 'skip': 'only canonical-plus-extra-LF provenance loop'})
                return ast.copy_location(ast.Pass(), node)
            return self.generic_visit(node)
        def visit_Dict(self, node):
            fields = {k.value: v for k, v in zip(node.keys, node.values) if isinstance(k, ast.Constant)}
            if (isinstance(fields.get('name'), ast.Constant)
                    and fields['name'].value == 'degree-one transport provenance'):
                if not isinstance(fields.get('status'), ast.Constant) or fields['status'].value != 'PASS':
                    raise ValueError('Unexpected provenance status.')
                fields['status'].value = 'SKIPPED: line-ending/hash provenance excluded by intake instruction'
                self.statuses += 1
            return self.generic_visit(node)
        def visit_Call(self, node):
            if ast.unparse(node.func) == 'tempfile.TemporaryDirectory':
                self.temporary_calls += 1
                node.func = ast.copy_location(ast.Name(id='_RetainedTemporaryDirectory', ctx=ast.Load()), node.func)
            return self.generic_visit(node)
    transform = Adapter()
    tree = transform.visit(tree)
    if len(transform.edits) != 2 or transform.statuses != 1 or transform.temporary_calls != 1:
        raise ValueError('Unexpected source50 replay driver; review adapter.')
    class RetainedTemporaryDirectory:
        def __init__(self, *args, **kwargs):
            replay.mkdir()
            self.name = str(replay)
        def __enter__(self):
            return self.name
        def __exit__(self, *args):
            return False
    adapter.write_text(json.dumps({
        'edits': transform.edits,
        'explicit_provenance_skip': True,
        'all_other_functional_assertions_retained': True,
        'temporary_directory': 'Retained outside checkout to preserve generated evidence; no source file changed'
    }, indent=2) + '\n')
    sys.argv = [str(script), '--output', str(output)]
    namespace = {'__name__': '__main__', '__file__': str(script),
                 '_RetainedTemporaryDirectory': RetainedTemporaryDirectory}
    exec(compile(ast.fix_missing_locations(tree), str(script), 'exec'), namespace)
    result = json.loads(output.read_text())
    if len(result['checks']) != 11 or sum(x['status'] == 'PASS' for x in result['checks']) != 10:
        raise ValueError('Expected10 substantive PASS and1 explicit provenance SKIP.')
    skipped = [x for x in result['checks'] if x['status'] != 'PASS']
    if len(skipped) != 1 or skipped[0]['name'] != 'degree-one transport provenance' or not skipped[0]['status'].startswith('SKIPPED:'):
        raise ValueError('Unexpected omitted substantive check.')
    print('Structured result:10 substantive PASS;1 provenance-only SKIP.', flush=True)


def degree1_comparison(package: Path, fresh: Path, output: Path) -> None:
    actual = json.loads(fresh.read_text())
    recorded = json.loads((package / 'machine_experiments/entry_degree1.json').read_text())
    keys = ('status', 'planned', 'pruned', 'remaining', 'nodes', 'affine_checks',
            'full_recheck_cases', 'groups', 'failures', 'frontier', 'survivors', 'blank_survivors')
    if any(actual[key] != recorded[key] for key in keys):
        raise ValueError('Fresh degree1 functional result differs from delivery.')
    if actual['status'] != 'completed' or actual['planned'] != 132048 or actual['affine_checks'] != 203162:
        raise ValueError('Degree1 did not complete the recorded family.')
    lines = byte_count = 0
    with fresh.with_suffix('.jsonl').open('rb') as new, gzip.open(package / 'machine_experiments/entry_degree1.jsonl.gz', 'rb') as old:
        for a, b in itertools.zip_longest(new, old):
            if a is None or a != b:
                raise ValueError(f'Degree1 journal differs at line{lines + 1}.')
            lines += 1
            byte_count += len(a)
    if lines != 132179:
        raise ValueError('Unexpected degree1 journal size.')
    output.write_text(json.dumps({'status': 'PASS', 'functional_keys_exact': list(keys),
                                 'journal_lines_byte_exact': lines, 'journal_bytes': byte_count,
                                 'recipes': 132048, 'affine_checks': 203162,
                                 'scope': 'Independent repetition of the source48-overlapping family; finite checker rejections are not mathematical counterexamples. No new machine or state lower bound.'}, indent=2) + '\n')


def main() -> None:
    if not __debug__:
        raise SystemExit('Keep assertions enabled; do not use -O or PYTHONOPTIMIZE.')
    sys.dont_write_bytecode = True
    if len(sys.argv) > 1 and sys.argv[1] == '_worker':
        if len(sys.argv) != 6:
            raise SystemExit('Expected worker package, result, replay, adapter paths.')
        functional_worker(*(Path(x).resolve() for x in sys.argv[2:]))
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--extended', action='store_true')
    parser.add_argument('--search-seconds', type=float, default=1000000,
                        help='Degree1 wall bound; a partial run fails the completed replay comparison.')
    args = parser.parse_args()
    repo = args.repo.resolve() if args.repo else next((p for p in Path(__file__).resolve().parents if (p / '.git').exists()), None)
    if repo is None:
        parser.error('Pass --repo when helper is outside the checkout.')
    if args.prepare_only and args.extended:
        parser.error('--prepare-only and --extended are exclusive.')
    if args.search_seconds <= 0:
        parser.error('--search-seconds must be positive.')
    work = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-batch157-reproduce-'))
    if work == repo or work.is_relative_to(repo) or (work.exists() and any(work.iterdir())):
        parser.error('Use a new or empty scratch directory outside the checkout.')
    work.mkdir(parents=True, exist_ok=True)
    package, mapping = recover(repo, work)
    record = {'batch': 157, 'source': 50, 'arrival': ARRIVAL, 'archive': ARCHIVE,
              'scratch': str(work), 'package': str(package),
              'recovery_counts': mapping['counts'],
              'recovered_path_map': str(work / 'recovered-paths.json'),
              'checks': [], 'Lean_built': False, 'Coq_built': False,
              'scope': 'Offline exact recovery and finite functional replay; default replays delivered degree1/degree2 partitions, extended repeats only degree1. No new machine/calibration/internal PA proof.',
              'provenance_skip': 'Only named degree-one extra-LF provenance input/loop, removed in memory; functional identities and assertions retained.'}
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    environment.pop('PYTHONOPTIMIZE', None)
    def run(name: str, command: list[str]) -> None:
        begun = time.monotonic()
        log = work / (name + '.log')
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=package, env=environment, stdout=stream, stderr=subprocess.STDOUT)
        record['checks'].append({'name': name, 'command': command, 'returncode': result.returncode,
                                 'seconds': round(time.monotonic() - begun, 3), 'log': str(log)})
        (work / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
        print(name, 'exit', result.returncode, flush=True)
        if result.returncode:
            raise SystemExit(f'{name} failed; inspect{log}.')
    if not args.prepare_only:
        output = work / 'source50-default.json'
        run('50-default', [sys.executable, '-B', str(Path(__file__).resolve()), '_worker',
                           str(package), str(output), str(work / 'isolated-replay'), str(work / 'adapter.json')])
        record['default_result'] = json.loads(output.read_text())
        record['adapter'] = json.loads((work / 'adapter.json').read_text())
    if args.extended:
        fresh = work / 'degree1-fresh.json'
        run('50-degree1-search', [sys.executable, '-B', str(package / 'machine_experiments/entry_resynthesis.py'),
                                  '--repo', str(package / 'reference/proveit'), '--degree', '1',
                                  '--output', str(fresh), '--seconds', str(args.search_seconds)])
        start = time.monotonic()
        degree1_comparison(package, fresh, work / 'degree1-comparison.json')
        record['checks'].append({'name': '50-degree1-comparison', 'returncode': 0,
                                 'seconds': round(time.monotonic() - start, 3),
                                 'result': str(work / 'degree1-comparison.json')})
        record['extended_result'] = json.loads((work / 'degree1-comparison.json').read_text())
    record['status'] = 'PREPARED' if args.prepare_only else 'PASS'
    (work / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('Evidence:', work, flush=True)


if __name__ == '__main__':
    main()
