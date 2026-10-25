#!/usr/bin/env python3
"""Read-only exact replay of the selected direct integer constructions.

No file is written unless --receipt is supplied. No network is used. This
script imports independently written coefficient/checking code, not build.py.
It verifies finite algebra, not consistency or the existence of a zero.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import review_direct_pools as R
import independent_algebra as A

PINS={
    'inherited/guarded.json':'c1a80140106a91997025501852b22526bc0072921f82f6b39d9a06cb07b26128',
    'inherited/source_certificate.json':'218e21b1843848a21c90b67b652865f0acfa5e72bafe353a9c5fc018e9db1c76',
}
VARIANTS=('odd_three_pools','four_pools')

def check(root,variants):
    pins={}
    for relative,expected in PINS.items():
        actual=hashlib.sha256((root/relative).read_bytes()).hexdigest()
        R.need(actual==expected,'Inherited source pin mismatch: '+relative)
        pins[relative]=actual
    report={'status':'PASS','python_optimized':bool(sys.flags.optimize),
            'source_pins':pins,'variants':{}}
    for variant in variants:
        p=root/variant
        result=R.run(root,variant)
        # Unlike a patch-only replay, this inherited independent checker
        # also validates the algebraic restrictions on the Horn refactoring.
        result['factorization_identity_changes']=A.factorization(
            A.get(p/'source.json'),A.get(p/'factored_source.json'),
            A.get(p/'factorization_certificate.json'))
        result['scope']='Exact source delta, source pins, complete Horn factorization identities, all monic restorations, all translations, full quartic expansion, refreshed-hash mutation rejection.'
        report['variants'][variant]=result
    report['boundary']='These finite checks do not prove the unbounded arithmetic or logical calibration; see PROOF.md and the retained source proofs.'
    return report

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=HERE)
    ap.add_argument('--variant',choices=VARIANTS,action='append')
    ap.add_argument('--receipt',type=Path)
    options=ap.parse_args()
    report=check(options.root,options.variant or VARIANTS)
    text=json.dumps(report,sort_keys=True,indent=2)+'\n'
    if options.receipt:
        options.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
