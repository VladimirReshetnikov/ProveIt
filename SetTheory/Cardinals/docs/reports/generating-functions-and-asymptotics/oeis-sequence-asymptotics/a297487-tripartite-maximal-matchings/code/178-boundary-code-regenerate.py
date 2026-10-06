#!/usr/bin/env python3
"""Recompute Report178 exact finite-check data; existing outputs are never replaced."""
import argparse
from pathlib import Path
import json
import os
import stat
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,help='new output file; its parent must exist')
    p.add_argument('--compare',type=Path,help='existing certificate to compare exactly')
    args=p.parse_args()
    if args.output:
        target=args.output.absolute()
        verify.need('..' not in target.parts,'unsafe output path')
        for parent in reversed(target.parents):
            verify.need(stat.S_ISDIR(parent.lstat().st_mode),'symlinked/nonregular output parent')
        verify.need(not os.path.lexists(target),'output already exists')
    verify.self_tests();data=verify.derive()
    if args.compare:verify.same(data,verify.load_certificate(args.compare))
    if args.output:
        with target.open('x',encoding='utf-8') as handle:handle.write(verify.canonical(data))
    print(json.dumps({'status':'PASS','report':178,'boundary_order':4,'certificate_compared':bool(args.compare),'certificate_written':bool(args.output),'method':'Exact Q(a), rational polynomial, Gaussian/Poisson moment and graph recurrences'},sort_keys=True))

if __name__=='__main__':
    try:main()
    except (verify.VerificationError,ValueError,TypeError,KeyError,OSError) as exc:
        print('REGENERATION FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
