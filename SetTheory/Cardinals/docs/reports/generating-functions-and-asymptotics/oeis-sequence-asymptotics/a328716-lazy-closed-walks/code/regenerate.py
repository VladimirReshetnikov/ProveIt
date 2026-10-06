#!/usr/bin/env python3
"""Regenerate exact certificates without modifying an existing file."""
import argparse
import json
import os
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='new output file outside the package')
    parser.add_argument('--compare',type=Path,help='certificate to compare exactly')
    args = parser.parse_args()
    if args.output:
        target = args.output.absolute()
        verify.files.check_directory(target.parent)
        verify.need('..' not in target.parts,'unsafe output path')
        verify.need(not os.path.lexists(target),'output already exists')
        verify.need(not target.resolve().is_relative_to(verify.ROOT.resolve()),'output must be outside package')
    data = verify.derive()
    if args.compare: verify.same(data,verify.load_certificate(args.compare))
    if args.output:
        with target.open('x',encoding='utf-8') as handle: handle.write(verify.canonical(data))
    print(json.dumps({'status':'PASS','report':179,'exact_order_checked':3,
                     'certificate_compared':bool(args.compare),'certificate_written':bool(args.output)},sort_keys=True))

if __name__ == '__main__':
    try: main()
    except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError) as exc:
        print('REGENERATION FAILED: '+str(exc),file=sys.stderr)
        sys.exit(1)
