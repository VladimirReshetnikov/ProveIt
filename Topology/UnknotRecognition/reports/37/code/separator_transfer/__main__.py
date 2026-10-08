"""CLI for the exponential validation recognizer and portable certificates."""
import argparse, json
from pathlib import Path
from .certificates import make_braid_certificate, verify_braid_certificate

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command',required=True)
    make = sub.add_parser('braid',help='small-input EXACT EXPONENTIAL reference recognizer')
    make.add_argument('--strands',type=int,required=True)
    make.add_argument('--word',required=True,help='JSON list, e.g. "[1,-2,1,-2]"')
    make.add_argument('--certificate',type=Path,required=True)
    make.add_argument('--matching-edge-limit',type=int)
    check = sub.add_parser('verify'); check.add_argument('certificate',type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'braid':
            data = make_braid_certificate(args.strands,json.loads(args.word),args.matching_edge_limit)
            args.certificate.write_text(json.dumps(data,indent=2)+'\n')
            print(json.dumps({k:data[k] for k in ('verdict','reduced_rank','sharp_lower')},indent=2))
        else:
            ok = verify_braid_certificate(json.loads(args.certificate.read_text()))
            print('VERIFIED' if ok else 'INVALID')
            return 0 if ok else 1
        return 0
    except (ValueError,TypeError,OSError,ArithmeticError) as exc:
        parser.exit(2,str(exc)+'\n')

if __name__ == '__main__': raise SystemExit(main())
