#!/usr/bin/env python3
"""Verify the delivered source transformations, projections and coefficients.

Python standard library only.  No network access, proof search, or proof
assistant is required.  Finite checks complement the ordinary proofs.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def run(arguments):
    completed = subprocess.run([sys.executable, '-B', *map(str, arguments)],
                               cwd=ROOT, text=True, capture_output=True)
    require(completed.returncode == 0, '\n'.join([str(arguments), completed.stdout, completed.stderr]))
    print(json.dumps({'check':str(arguments[0]), 'status':'PASS'}), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, help='optional permanent receipt directory')
    ap.add_argument('--rebuild', action='store_true', help='also regenerate the equations')
    args = ap.parse_args()
    manifest_path = ROOT/'MANIFEST.json'
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_bytes())
        for name, expected in manifest['sha256'].items():
            actual = sha256((ROOT/name).read_bytes()).hexdigest()
            require(actual == expected, 'file checksum mismatch: '+name)
        print(json.dumps({'check':'complete file inventory', 'status':'PASS', 'files':len(manifest['sha256'])}), flush=True)
    archive = ROOT/'quotient_frame/provenance/ConZFC_407_888_Quartics_2026-10-24.zip'
    require(archive.is_file(), 'frozen source archive')
    with tempfile.TemporaryDirectory(prefix='conzfc-verify-') as temporary:
        receipts = args.output.resolve() if args.output else Path(temporary)
        receipts.mkdir(parents=True, exist_ok=True)
        for folder in ['quotient_frame', 'signed_frame']:
            run(['review/peer_check.py', '--package', ROOT/folder, '--archive', archive,
                 '--output', receipts/(folder+'_source.json')])
            run(['check_projection_independent.py', ROOT/folder,
                 '--output', receipts/(folder+'_projection.json')])
            if args.rebuild:
                run([ROOT/folder/'build.py', '--check'])
        require((ROOT/'height_two/anchored/source.json').read_bytes() ==
                (ROOT/'signed_frame/parent.json').read_bytes(), 'height-two source identity')
        run(['height_two/verify.py', 'height_two/anchored', '--mutations'])
        if args.rebuild:
            rebuilt = Path(temporary)/'height_rebuilt'
            run(['height_two/build.py', 'height_two/anchored/source.json', rebuilt, '--anchor-linear'])
            for name in ['source.json','equation.json','certificate.json','expanded_polynomial.json','BUILD.json']:
                require((rebuilt/name).read_bytes() == (ROOT/'height_two/anchored'/name).read_bytes(),
                        'height-two exact rebuild '+name)
        summary = {'status':'PASS', 'source_variants':2, 'projected_polynomials':4,
                   'height_two_polynomials':1, 'rebuild':args.rebuild,
                   'scope':'Finite source identities, exact integer projections, full coefficients and unit pullbacks; ordinary proofs are in report.'}
        if args.output:
            (receipts/'SUMMARY.json').write_text(json.dumps(summary, indent=2)+'\n')
        print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
