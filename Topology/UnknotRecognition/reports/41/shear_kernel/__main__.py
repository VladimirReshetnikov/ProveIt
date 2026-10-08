"""Command-line demonstration and offline abstract-presentation trace verifier."""
from pathlib import Path
import argparse,json,sys
from .slp import Grammar
from .presentation import reduce_presentation,verify_presentation_reduction
from .flow import WorkLimit

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    verify=sub.add_parser('verify',help='verify an abstract-presentation trace, not knot provenance')
    verify.add_argument('file',type=Path)
    verify.add_argument('--max-bytes',type=int,default=50_000_000)
    demo=sub.add_parser('demo',help='generate a succinct infinite-cyclic presentation and trace')
    demo.add_argument('--bits',type=int,default=100)
    demo.add_argument('--branches',type=int,default=6)
    demo.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:
        if args.command=='verify':
            if args.max_bytes<0 or args.file.stat().st_size>args.max_bytes:
                raise ValueError('input byte allowance exceeded')
            payload=json.loads(args.file.read_text())
            if set(payload)!={'source_contract','grammar','generators','reduction'}:
                raise ValueError('invalid presentation bundle schema')
            g,roots=Grammar.from_dict(payload['grammar'])
            verify_presentation_reduction(g,roots,payload['generators'],payload['reduction'])
        else:
            if not 1<=args.bits<=10000 or not 1<=args.branches<=100:
                raise ValueError('demo requires 1 <= bits <= 10000 and 1 <= branches <= 100')
            g=Grammar(); roots=[]; generators=list(range(1,args.branches+2))
            for j in range(2,args.branches+2):
                node=g.concat(g.letter(j),g.run(1,2**args.bits+j))
                roots.extend([g.power(node,2**args.bits+j),g.power(node,2**args.bits+j+1)])
            _,_,record=reduce_presentation(g,roots,generators)
            payload={'source_contract':'abstract group presentation; no knot provenance claimed',
                     'grammar':g.to_dict(roots),'generators':generators,'reduction':record}
            verify_presentation_reduction(g,roots,generators,record)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps(payload,indent=2)+'\n')
        terminal=payload['reduction']['terminal']
        print(json.dumps({'verified':True,'scope':'abstract presentation only; no knot verdict',
                          'status':payload['reduction']['status'],
                          'shear_phases':len(payload['reduction']['steps']),
                          'is_infinite_cyclic':None if terminal is None else terminal['is_infinite_cyclic']},indent=2))
        return 0
    except (OSError,ValueError,KeyError,TypeError,WorkLimit) as exc:
        print(f'No verdict: {exc}',file=sys.stderr); return 2
if __name__=='__main__': raise SystemExit(main())
