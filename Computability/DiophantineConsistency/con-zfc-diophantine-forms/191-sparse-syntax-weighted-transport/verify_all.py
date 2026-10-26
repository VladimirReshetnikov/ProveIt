#!/usr/bin/env python3
"""Offline exact release checks; no root search and no formal-kernel claim."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
EXCLUDED_SUFFIXES = {'.aux', '.log', '.toc', '.out', '.fls', '.fdb_latexmk', '.pyc'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify_manifest():
    manifest = ROOT/'MANIFEST.sha256'
    require(manifest.is_file(), 'Missing MANIFEST.sha256')
    recorded = set()
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT/name
        require(not Path(name).is_absolute() and '..' not in Path(name).parts,
                'Invalid manifest path')
        require(name not in recorded, 'Repeated manifest path')
        recorded.add(name)
        require(path.is_file(), 'Missing release file: '+name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                'Changed release file: '+name)
    actual = {path.relative_to(ROOT).as_posix() for path in ROOT.rglob('*')
              if path.is_file() and path.name != 'MANIFEST.sha256'
              and path.suffix not in EXCLUDED_SUFFIXES
              and '__pycache__' not in path.parts}
    require(recorded == actual, 'Manifest does not cover exactly the release files')
    return {'status': 'PASS', 'files': len(recorded)}


def run_script(name, *arguments):
    command = [sys.executable]
    if sys.flags.optimize:
        command.append('-O')
    command.extend(['-B', str(ROOT/name), *arguments])
    run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    require(run.returncode == 0,
            'Failed '+name+'\n'+run.stdout+'\n'+run.stderr)
    try:
        return json.loads(run.stdout)
    except json.JSONDecodeError:
        return {'status': 'PASS', 'output': run.stdout.strip()}


def bindings():
    endpoint = ROOT/'direct208/equations/principal208'
    metrics = json.loads((endpoint/'metrics.json').read_text())
    require(metrics == {'variables': 208, 'rows': 148, 'degree': 4,
                        'monomials': 5987, 'height': 2**44, 'row_height': 2**22},
            'Unexpected principal quartic metrics')
    text = (ROOT/'report/metrics.tex').read_text()
    macros = dict(re.findall(r'\\newcommand\{\\(\w+)\}\{([^{}]*)\}', text))
    require({key: macros.get(key) for key in ['DirectVariables', 'DirectRows',
             'DirectLastRow', 'DirectLastVariable', 'DirectMonomials']} ==
            {'DirectVariables':'208', 'DirectRows':'148', 'DirectLastRow':'147',
             'DirectLastVariable':'207', 'DirectMonomials':'5,987'},
            'Printed direct metric mismatch')
    require(r'\newcommand{\DirectHeightMath}{\ensuremath{2^{44}}}' in text,
            'Printed height mismatch')
    require((ROOT/'report/residuals.tex').read_bytes() == (endpoint/'residuals.tex').read_bytes(),
            'Paper residuals differ from independently checked literal residuals')
    equation = json.loads((ROOT/'positive190/equation.json').read_text())
    require(equation['exact_degree'] == 190 and equation['operations'] == 120
            and len(equation['witnesses']) == 10
            and equation['domain'] == 'strictly positive integers',
            'Compact profile/domain mismatch')
    parent = ROOT/'dependencies/Pell_Growth_210_original.zip'
    # The original parent hash is bound both here and in the direct source ledger.
    ledger = json.loads((ROOT/'SOURCE_SNAPSHOT.json').read_text())
    require(hashlib.sha256(parent.read_bytes()).hexdigest() == ledger['parent_archive_sha256'],
            'Retained incoming parent archive mismatch')
    for component in ['positive190', 'direct208', 'affine209']:
        record = json.loads((ROOT/component/'SOURCES.json').read_text())
        recorded_snapshot = record.get('snapshot', record.get('commit', record.get('repository_commit')))
        if recorded_snapshot is not None:
            require(recorded_snapshot == ledger['repository_commit'], 'Source snapshot mismatch')
    return {'status': 'PASS', 'quartic': metrics,
            'compact': {'positive_variables': 10, 'degree': 190, 'operations': 120},
            'printed_residuals': 148, 'parent_archive_sha256': ledger['parent_archive_sha256']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-manifest', action='store_true',
                        help='For an intentional edit before regenerating the release manifest')
    parser.add_argument('--manifest-only', action='store_true')
    args = parser.parse_args()
    require(not (args.skip_manifest and args.manifest_only), 'Conflicting manifest options')
    if args.manifest_only:
        print(json.dumps(verify_manifest(), sort_keys=True))
        return
    checks = {}
    checks['direct208'] = run_script('direct208/verify.py')
    checks['positive190_build'] = run_script('positive190/build.py', '--check')
    checks['positive190'] = run_script('positive190/verify.py')
    checks['fixed_coefficients'] = run_script('positive190/rebuild_coefficients.py')
    checks['affine209'] = run_script('affine209/verify.py')
    checks['independent_center'] = run_script('reviews/check_center190.py')
    checks['independent_depth'] = run_script('reviews/check_sparse_depth.py',
        str(ROOT/'direct208/local_compiler.py'), str(ROOT/'reviews/sparse_source.py'))
    checks['document_bindings'] = bindings()
    checks['manifest'] = {'status': 'DEFERRED'} if args.skip_manifest else verify_manifest()
    result = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize), 'checks': checks,
              'scope': 'Exact finite algebra, source and artifact binding; the unbounded mathematical arguments and inherited logical calibrations are separate.'}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
