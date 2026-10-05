#!/usr/bin/env python3
"""Regenerate finite exact certificates to a new file; never overwrite."""
from __future__ import annotations
import argparse
import os
from pathlib import Path
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--compare',type=Path)
    args=parser.parse_args()
    try:
        output=args.output.absolute()
        verify.need('..' not in output.parts,'unsafe output path')
        verify.files.check_directory(output.parent)
        verify.need(not os.path.lexists(output),'refusing existing output')
        verify.need(not output.resolve().is_relative_to(verify.ROOT.resolve()),
                    'regeneration output must be outside the package')
        value=verify.derive()
        if args.compare is not None:
            verify.same(value,verify.load_certificate(args.compare))
        with output.open('xb') as stream:
            stream.write(verify.canonical(value))
        print(verify.canonical({'status':'PASS','report':182,'regenerated':True,
                                'comparison_requested':args.compare is not None}).decode(),end='')
    except (ValueError,RuntimeError,TypeError,KeyError,IndexError,OSError) as exc:
        print('REGENERATION FAILED: '+str(exc),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    sys.exit(main())
