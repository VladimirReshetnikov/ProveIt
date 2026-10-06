#!/usr/bin/env python3
"""Build deterministic Report 170 verification results; never overwrite a directory."""
import argparse
import json
from pathlib import Path
import platform
import sys
import sympy
import mpmath
from common import ROOT, canonical_json, require, sha256, validate_fixtures
import exact_counts
import exact_algebra
import independent_series
import diagnostics
from release_tools import parent_handle, fresh_directory, write_member
import os
import hashlib


def bounded_terms(text):
    value = int(text)
    if not 8 <= value <= 240:
        raise argparse.ArgumentTypeError('terms must lie in 8..240 (default: 200)')
    return value


def input_hashes():
    paths = list(ROOT.glob('*.py'))+[ROOT/'README.md', ROOT/'requirements.txt']+list((ROOT/'fixtures').glob('*'))
    return {str(path.relative_to(ROOT)): sha256(path) for path in sorted(paths) if path.is_file()}


def build(output, terms):
    output = Path(output)
    require(not output.exists(), 'Refusing to overwrite existing output directory: '+str(output))
    with parent_handle(output) as (_, parent, leaf):
        try:
            os.stat(leaf, dir_fd=parent, follow_symlinks=False)
        except FileNotFoundError:
            pass
        else:
            raise RuntimeError('Refusing to overwrite existing output')
    validate_fixtures()
    counts = exact_counts.run(terms)
    algebra = exact_algebra.run()
    independent = independent_series.run(algebra)
    finite = diagnostics.run(counts, algebra)
    files = {'exact_counts.json': counts, 'exact_algebra.json': algebra,
             'independent_series.json': independent, 'finite_diagnostics.json': finite}
    serialized = {name: canonical_json(value) for name, value in files.items()}
    manifest = {'format': 'Report 170 deterministic companion results v1',
                'terms': terms, 'correction_order': 4,
                'runtime_versions': {'python': platform.python_version(), 'sympy': sympy.__version__, 'mpmath': mpmath.__version__},
                'input_sha256': input_hashes(),
                'artifact_sha256': {name: hashlib.sha256(content).hexdigest() for name, content in sorted(serialized.items())},
                'status': 'Exact identities and finite numerical cross-checks passed; numerical values are not interval certificates'}
    serialized['manifest.json'] = canonical_json(manifest)
    serialized['SHA256SUMS'] = ''.join(hashlib.sha256(content).hexdigest()+'  '+name+'\n' for name, content in sorted(serialized.items())).encode('ascii')
    # Every parent component rejects symlinks; the descriptor stays pinned and
    # exclusive directory/member creation handles races without overwriting.
    with fresh_directory(output) as (_, descriptor):
        for name, content in sorted(serialized.items()):
            write_member(descriptor, name, content)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terms', type=bounded_terms, default=200, help='positive indices computed, 8..240; 200 verifies all archived OEIS terms')
    parser.add_argument('--output', type=Path, default=ROOT/'results-local', help='new directory; existing paths are always rejected')
    args = parser.parse_args()
    try:
        build(args.output, args.terms)
    except (RuntimeError, ValueError, OSError) as exc:
        print('FAIL: '+str(exc), file=sys.stderr)
        return 1
    print('PASS: exact identities, '+str(min(args.terms, 200))+' positive terms per OEIS sequence, independent numerical comparisons; diagnostic results are not certificates')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
