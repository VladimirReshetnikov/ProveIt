"""Usage: python -m ordered_kernel example.json [--method ordered]."""
import argparse,sys
from pathlib import Path
from . import optimize_counts,Limits,transport_counts
from .jsonio import loads,dumps,parse_input

def main():
    parser=argparse.ArgumentParser(description='Exact local deferral, never a knot verdict')
    parser.add_argument('input',type=Path)
    parser.add_argument('--method',choices=['auto','ordered','two-incidence'],default='auto')
    parser.add_argument('--max-states',type=int,default=250000)
    parser.add_argument('--max-work',type=int,default=20000000)
    parser.add_argument('--max-width',type=int,default=9)
    parser.add_argument('--exact-counts',action='store_true')
    args=parser.parse_args()
    try:
        if args.input.stat().st_size>32*1024*1024:
            raise ValueError('CLI input exceeds 32 MiB admission cap')
        counts,weights=parse_input(loads(args.input.read_text()))
        plan=optimize_counts(counts,weights,method=args.method,
                             limits=Limits(args.max_states,args.max_work,args.max_width))
        if plan['status']=='OPTIMAL_MATRIX_PLAN':
            residual=transport_counts(counts,plan,weights=weights,saturated=not args.exact_counts)
            plan['residual_count_rows']=[{'id':r,'entries':[[c,a] for c,a in sorted(row.items())]}
                                         for r,row in sorted(residual.items())]
        sys.stdout.write(dumps(plan))
        return 0 if plan['status']=='OPTIMAL_MATRIX_PLAN' else 2
    except (ValueError,OSError) as exc:
        parser.exit(2,f'error: {exc}\n')

if __name__=='__main__':raise SystemExit(main())
