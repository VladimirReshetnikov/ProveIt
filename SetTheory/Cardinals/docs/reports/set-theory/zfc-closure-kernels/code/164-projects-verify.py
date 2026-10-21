#!/usr/bin/env python3
"""Replay the compact evidence, with optional fresh symbolic runtime derivation.

Python 3, standard library only. The large physical searches and PDF build
are separate, explicit operations documented in README.md.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_metrics(rows):
    by_path = {p: (op, arg) for p, op, arg in rows}
    assert len(by_path) == len(rows)
    found = []
    distinct = set()

    def visit(path=''):
        if path in by_path:
            node = by_path[path]
            found.append([path, *node])
        else:
            assert any(p.startswith(path) for p in by_path), path
            node = (visit(path + '0'), visit(path + '1'))
        distinct.add(node)
        return node

    visit()
    assert found == rows
    return {
        'dag_nodes': len(distinct),
        'leaf_occurrences': len(rows),
        'maximum_depth': max(len(p) for p, _, _ in rows),
        'maximum_zero_run': max(len(run) for p, _, _ in rows for run in p.split('1')),
        'guarded_cases': sum(2 if op == 'CD' else 1 for _, op, _ in rows),
    }


def table_metrics(path, halt):
    table = {}
    for line in path.read_text().splitlines():
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        q, r, w, direction, z = line.split()
        q, r, w, z = map(int, (q, r, w, z))
        assert r in (0, 1) and w in (0, 1) and direction in ('L', 'R')
        assert (q, r) not in table
        table[q, r] = (w, direction, z)
    states = {q for q, _ in table}
    assert halt not in states
    assert all((q, b) in table for q in states for b in (0, 1))
    assert all(z in states or z == halt for _, _, z in table.values())
    reached = {0}
    queue = [0]
    for q in queue:
        for b in (0, 1):
            z = table[q, b][2]
            if z != halt and z not in reached:
                reached.add(z)
                queue.append(z)
    assert reached == states
    return {'working_states': len(states), 'rows': len(table)}


def run_json(script, arguments, output):
    proc = subprocess.run([sys.executable, '-B', str(script), *map(str, arguments)],
                          cwd=ROOT, text=True, capture_output=True)
    if proc.returncode:
        raise RuntimeError(f'{script.name} failed ({proc.returncode}):\n{proc.stdout}\n{proc.stderr}')
    return json.loads(output.read_text()) if output.exists() else json.loads(proc.stdout)


def main():
    if not __debug__:
        raise SystemExit('Run without -O or PYTHONOPTIMIZE; assertions are proof checks.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write a fresh receipt outside the pinned packet.')
    parser.add_argument('--skip-manifest', action='store_true', help='For development after intentional edits.')
    parser.add_argument('--runtime', action='store_true', help='Freshly derive all 6,176 universal cases for the new primary 215-state candidate.')
    parser.add_argument('--upstream-runtime', action='store_true', help='Freshly derive all 6,176 cases for the credited late 216-state construction.')
    args = parser.parse_args()
    report = {'status': 'PASS', 'scope': 'New 215-state exact composition, additional calculus results, and credited parent216 replay. Foundational calibration remains pinned and inherited.'}

    manifest = ROOT / 'MANIFEST.json'
    if not args.skip_manifest:
        entries = json.loads(manifest.read_text())['files']
        for item in entries:
            p = ROOT / item['path']
            assert p.is_file(), item['path']
            assert p.stat().st_size == item['bytes'], ('size', item['path'])
            assert digest(p) == item['sha256'], ('sha256', item['path'])
        report['manifest_files_verified'] = len(entries)

    baseline = ROOT / 'baseline'
    pins = {
        'k217.native.tm': 'b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088',
        'k217.tm': '522a71c067afe8862c9aab98e0f7f93eac747f5ef91d26bd3568760e1c1c478f',
        'sites217.json': '9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655',
    }
    for name, expected in pins.items():
        assert digest(baseline / name) == expected
    report['native_baseline'] = table_metrics(baseline / 'k217.native.tm', 254)
    report['canonical_baseline'] = table_metrics(baseline / 'k217.tm', 217)
    assert report['native_baseline'] == report['canonical_baseline'] == {'working_states': 217, 'rows': 434}
    report['baseline_source'] = source_metrics(json.loads((baseline / 'sites217.json').read_text()))
    assert report['baseline_source'] == {
        'dag_nodes': 203, 'leaf_occurrences': 4751, 'maximum_depth': 45,
        'maximum_zero_run': 6, 'guarded_cases': 6176,
    }

    sys.path.insert(0, str(ROOT / 'theory'))
    audit = load_module('packet_projection_audit', ROOT / 'theory' / 'audit_projection_basis.py')
    certificate = ROOT / 'theory' / 'dominated_rho8_full_certificate.json'
    assert digest(certificate) == '3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452'
    projection = audit.audit(certificate)
    assert projection == json.loads((ROOT / 'results' / 'projection_basis_audit.json').read_text())
    report['projection_theorem'] = {
        'proof_nodes': projection['forward_proof']['proof_nodes'],
        'shared_terms': projection['forward_proof']['shared_terms'],
        'covered_axiom_leaves': len(projection['leaves']),
        'minimum_support_for_fixed_certificate': 9,
        'minimum_covers': len(projection['literal_cover_minimum']['all_six_optimal_covers']),
    }

    matrix = load_module('packet_context_matrix', ROOT / 'theory' / 'check_context_countermodel.py')
    assert matrix.check()['verified']
    report['context_matrix'] = 'PASS; stated total raw-code projection families, with full native calculus and generalization excluded'

    with tempfile.TemporaryDirectory(prefix='proveit-research-verify-') as temp:
        work = Path(temp)
        independent = run_json(ROOT / 'review' / 'review_projector_certificate.py',
                               ['--certificate', certificate, '--output', work / 'projection.json'],
                               work / 'projection.json')
        assert independent['minimum_literal_certificate_cover'] == 9
        assert independent['proof_nodes'] == 3728
        assert len(independent['optimal_covers']) == 6
        report['independent_projection_review'] = independent['status']
        context = run_json(ROOT / 'review' / 'review_context_matrix.py',
                           ['--output', work / 'matrix.json'], work / 'matrix.json')
        report['independent_context_review'] = context['status']
        lifting = run_json(ROOT / 'review' / 'review_matrix_lifting.py',
                           ['--output', work / 'lifting.json'], work / 'lifting.json')
        assert lifting['raw_family_cases'] == 524288
        report['independent_raw_code_lifting'] = lifting['status']

        residual = run_json(ROOT / 'theory' / 'check_residual_contracts.py',
                            [work / 'residual.json'], work / 'residual.json')
        assert residual['status'] == 'PASS'
        assert residual == json.loads((ROOT / 'results' / 'residual_contracts_check.json').read_text())
        report['residual_command_contracts'] = {
            'status': residual['status'], 'tests': residual['total_tests'],
            'scope': 'Finite exact command-interface checks; universal proof is in the report.',
        }

        scanner_script = ROOT / 'review' / 'review_short_scanner.py'
        if scanner_script.exists():
            scanner = run_json(scanner_script,
                               ['--baseline', baseline, '--output', work / 'scanner.json'],
                               work / 'scanner.json')
            report['scanner_counterexample'] = scanner.get('status', 'REPRODUCED')

        source_script = ROOT / 'search' / 'source' / 'reproduce.py'
        if source_script.exists():
            source = run_json(source_script, ['--output', work / 'source'], work / 'source' / 'findings.json')
            report['source_experiments'] = source.get('status', 'REPRODUCED')

        primary_args = ['--output', work / 'candidate215']
        if args.runtime:
            primary_args.append('--runtime')
        primary = run_json(ROOT / 'candidate215/replay.py', primary_args, work / 'candidate215/result.json')
        assert primary['working_states'] == 215 and primary['rows'] == 430
        report['new_primary215'] = primary

        late_args = ['--output', work / 'upstream216']
        if args.upstream_runtime:
            late_args.append('--runtime')
        late = run_json(ROOT / 'upstream216/replay.py', late_args, work / 'upstream216/result.json')
        assert late['working_states'] == 216 and late['rows'] == 432
        report['credited_upstream216'] = late

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
