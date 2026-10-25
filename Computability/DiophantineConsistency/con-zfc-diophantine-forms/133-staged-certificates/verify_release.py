#!/usr/bin/env python3
"""Verify the release and replay exact finite checks, without network access."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(value, message):
    if not value:
        raise ValueError(message)


def manifest():
    path = ROOT/'MANIFEST.sha256'
    require(path.is_file(), 'Release manifest is missing')
    count = 0
    for line in path.read_text().splitlines():
        digest, rel = line.split('  ', 1)
        p = ROOT/rel
        require(p.resolve().is_relative_to(ROOT.resolve()), 'Invalid manifest path')
        require(p.is_file(), 'Missing file: ' + rel)
        require(hashlib.sha256(p.read_bytes()).hexdigest() == digest, 'Changed file: ' + rel)
        count += 1
    return count


def metadata():
    results = json.loads((ROOT/'RESULTS.json').read_text())
    for name, summary in results['direct'].items():
        path = ROOT/summary['path']
        data = json.loads(path.read_text())
        metrics = data['metrics']
        for key, source in [('variables', 'variables'), ('quadratic_residuals', 'quadratic_rows'),
                            ('exact_degree', 'exact_degree'), ('expanded_monomials', 'expanded_monomials'),
                            ('coefficient_height', 'max_abs_expanded_coefficient')]:
            require(summary[key] == metrics[source], 'Incorrect result metadata: '+name+'/'+key)
        require(summary['sha256'] == hashlib.sha256(path.read_bytes()).hexdigest(),
                'Incorrect equation digest: '+name)
    for name, summary in results['compact'].items():
        path = ROOT/summary['path']
        data = json.loads(path.read_text())
        require(summary['variables'] == len(data['witnesses']), 'Incorrect compact dimension')
        require(summary['binary_operations'] == data['operations'], 'Incorrect operation count')
        require(summary['operation_breakdown'] == data['operation_breakdown'], 'Incorrect operation breakdown')
        require(summary['exact_degree'] == data['exact_degree'], 'Incorrect compact degree')
        require(summary['sha256'] == hashlib.sha256(path.read_bytes()).hexdigest(),
                'Incorrect compact digest: '+name)
    companion = json.loads((ROOT/'integer_companion.json').read_text())
    source = json.loads((ROOT/companion['source_equation']).read_text())
    n = len(source['variables'])
    require(companion['variables'] == 3*n, 'Incorrect integer companion dimension')
    require(companion['exact_degree'] == 2*source['metrics']['exact_degree'], 'Incorrect companion degree')
    expected = [{'source_coordinate': j,
                 'terms': [[1, [3*j, 3*j]], [1, [3*j+1, 3*j+1]],
                           [1, [3*j+2, 3*j+2]], [1, [3*j+2]]]}
                for j in range(n)]
    require(companion['substitution'] == expected, 'Incorrect integer companion substitution')
    return {'status': 'PASS', 'direct_summaries': len(results['direct']),
            'compact_summaries': len(results['compact']), 'integer_companion_substitutions': n}


def check(rebuild):
    files = manifest()
    literal_metadata = metadata()
    stages = []
    with tempfile.TemporaryDirectory(prefix='conzfc-final-replay-') as td:
        temp = Path(td)
        for optimized in (False, True):
            prefix = [sys.executable, '-B'] + (['-O'] if optimized else [])
            for label, script, args in [
                ('direct', 'direct/verify.py', ['--receipt', str(temp/('direct-'+str(optimized)+'.json'))] + (['--rebuild'] if rebuild else [])),
                ('compact', 'compact/verify.py', ['--output', str(temp/('compact-'+str(optimized)+'.json'))]),
                ('printed-residuals', 'report/generate_residuals.py', ['--check']),
            ]:
                command = prefix + [str(ROOT/script)] + args
                proc = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
                require(proc.returncode == 0, label+' failed:\n'+proc.stdout+'\n'+proc.stderr)
                result = json.loads(proc.stdout)
                stages.append({'stage': label, 'optimized': optimized,
                               'status': result.get('status'),
                               'stdout_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
                               'result': result})
    require(manifest() == files, 'Manifest changed during replay')
    return {'status': 'PASS', 'files_authenticated': files, 'direct_rebuilt': rebuild,
            'literal_metadata': literal_metadata,
            'stages': stages,
            'scope': 'literal arithmetic and source bindings; ordinary unbounded proofs and inherited calibration are separate'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    if args.receipt:
        require(not args.receipt.resolve().is_relative_to(ROOT.resolve()),
                'Save replay receipts outside the sealed release folder')
    result = check(args.rebuild)
    if args.receipt:
        args.receipt.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'files_authenticated': result['files_authenticated'],
                      'direct_rebuilt': result['direct_rebuilt'],
                      'stages': [{'stage': r['stage'], 'optimized': r['optimized'], 'status': r['status']} for r in result['stages']]}, indent=2))


if __name__ == '__main__':
    main()
