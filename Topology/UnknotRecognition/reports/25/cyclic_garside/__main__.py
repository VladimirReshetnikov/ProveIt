from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
from . import compress, verify, compress_radius, verify_radius, Budget, LimitExceeded, CertificateError
from .verify import VerificationLimit


def read_json(path):
    p=Path(path)
    if p.stat().st_size > 64*1024*1024:
        raise ValueError("JSON input exceeds the CLI's 64 MiB limit")
    return json.loads(p.read_text(encoding='utf-8'))


def main():
    parser=argparse.ArgumentParser(description='Verified cyclic braid kernel; not a standalone knot verdict.')
    sub=parser.add_subparsers(dest='command',required=True)
    make=sub.add_parser('compress')
    make.add_argument('input',help='JSON object with strands and word fields')
    make.add_argument('--linear',action='store_true')
    make.add_argument('--all-rotations',action='store_true',help='disable the exact lower-bound early exit')
    make.add_argument('--max-ticks',type=int)
    make.add_argument('--radius',type=int,default=1,help='target word radius; default 1, optional 2')
    make.add_argument('--max-targets',type=int,default=100000)
    make.add_argument('-o','--output')
    check=sub.add_parser('verify');check.add_argument('input');check.add_argument('certificate')
    args=parser.parse_args()
    try:
        data=read_json(args.input)
        if not isinstance(data,dict):
            raise ValueError('input must be a JSON object')
        if args.command=='compress':
            kwargs=dict(cyclic=not args.linear, stop_at_lower_bound=not args.all_rotations,
                        budget=Budget(args.max_ticks))
            if args.radius == 1:
                result=compress(data['strands'],data['word'],**kwargs)
                checker=verify
            else:
                result=compress_radius(data['strands'],data['word'],radius=args.radius,
                                       max_targets=args.max_targets,**kwargs)
                checker=verify_radius
            # Always replay before exporting an accepted optimization.
            checker(data['strands'],data['word'],result['certificate'])
            text=json.dumps(result,indent=2)+'\n'
            if args.output:
                Path(args.output).write_text(text,encoding='utf-8')
            else:
                print(text,end='')
        else:
            cert=read_json(args.certificate)
            if not isinstance(cert,dict):
                raise ValueError('certificate must be a JSON object')
            if 'certificate' in cert:
                cert=cert['certificate']
            if not isinstance(cert,dict):
                raise ValueError('certificate envelope must contain an object')
            checker=verify_radius if cert.get('schema')=='cyclic-garside-kernel-v2' else verify
            word=checker(data['strands'],data['word'],cert)
            print(json.dumps({'verified':True,'word':list(word),'scope':'braid equality after recorded rotation'}))
    except (KeyError,TypeError,ValueError,OSError,LimitExceeded,VerificationLimit) as exc:
        print(json.dumps({'error':str(exc),'knot_verdict':None}),file=sys.stderr)
        return 2
    return 0

if __name__=='__main__':
    raise SystemExit(main())
