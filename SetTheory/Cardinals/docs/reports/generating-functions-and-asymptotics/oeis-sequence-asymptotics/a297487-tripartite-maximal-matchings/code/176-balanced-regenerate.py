#!/usr/bin/env python3
"""Recompute the exact Report176 certificate with the Python standard library.

No output file is changed unless --output names a new file. --compare verifies
an existing certificate exactly. This script does not install or download code.
"""
import argparse
import json
from pathlib import Path
import sys
import verify


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='new certificate file; existing files are refused')
    parser.add_argument('--compare',type=Path,help='compare every generated field with this certificate')
    args=parser.parse_args()
    if args.output and (args.output.exists() or args.output.is_symlink()):
        parser.error('output already exists; choose a new file')
    verify.self_tests()
    data=verify.derive()
    if args.compare:verify.same(data,verify.load_certificate(args.compare))
    if args.output:
        with args.output.open('x',encoding='utf-8') as stream:stream.write(verify.canonical(data))
    print(json.dumps({'status':'PASS','report':176,'order':5,
                      'certificate_compared':bool(args.compare),'certificate_written':bool(args.output),
                      'method':'Exact rational polynomial and integer recurrences; no numerical fitting'},sort_keys=True,indent=2))

if __name__=='__main__':
    try:main()
    except (verify.VerificationError,ValueError,KeyError,TypeError,OSError) as exc:
        print('REGENERATION FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
