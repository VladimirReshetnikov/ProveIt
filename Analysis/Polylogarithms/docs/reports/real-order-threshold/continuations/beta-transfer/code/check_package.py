#!/usr/bin/env python3
"""Check delivered result receipts and, optionally, the immutable inventory.

Use --manifest before replaying or rebuilding. Replays on different Python,
SymPy, mpmath, or TeX versions may validly produce different output bytes.
Neither mode proves the analytic theorems in the article.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--manifest',action='store_true',help='verify the original delivered byte inventory')
    args=ap.parse_args()
    exact=json.loads((ROOT/'data'/'exact_certificates.json').read_text())
    symbolic=json.loads((ROOT/'data'/'symbolic_checks.json').read_text())
    cyclo=json.loads((ROOT/'data'/'cyclotomic_certificates.json').read_text())
    diagnostics=json.loads((ROOT/'data'/'diagnostics.json').read_text())
    build=json.loads((ROOT/'data'/'build_receipt.json').read_text())
    assert all(x['status']=='PASS' for x in [exact,symbolic,cyclo,diagnostics,build])
    assert len(exact['values'])==12
    assert symbolic['number_of_exact_checks']==176
    assert len(cyclo['cases'])==6
    assert sum(x['numerator_coefficient_equalities'] for x in cyclo['cases'])==548
    assert build['undefined_references']==0 and build['overfull_boxes']==0
    for name,key in [('beta_transfer.tex','source_sha256'),('beta_transfer.pdf','pdf_sha256')]:
        assert hashlib.sha256((ROOT/'article'/name).read_bytes()).hexdigest()==build[key]
    print('PASS result receipts: 12 value enclosures, 176 symbolic checks, 6 cyclotomic identities, diagnostics, PDF build')
    if args.manifest:
        names=[]
        for line in (ROOT/'MANIFEST.sha256').read_text().splitlines():
            digest,name=line.split('  ',1)
            path=ROOT/name
            assert path.is_file(),f'missing file: {name}'
            assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,f'checksum mismatch: {name}'
            names.append(name)
        actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()
                and p.name!='MANIFEST.sha256' and '__pycache__' not in p.parts}
        assert actual==set(names),'manifest inventory mismatch'
        print(f'PASS original SHA-256 inventory: {len(names)} files')
    print('Scope: receipt and integrity checks; not proof-assistant verification.')

if __name__=='__main__':main()
