#!/usr/bin/env python3
"""Refine reachable guard invariants with exact small constants."""
from pathlib import Path
import json,time
import reachable_guards as r
HERE=Path(__file__).resolve().parent

def main():
    parser=r.arguments(__doc__)
    parser.add_argument('--cutoffs',type=int,nargs='+',default=[2,3,4,8,16,32,64],
        help='Exact-value cutoffs; the remaining category is strictly larger.')
    args=parser.parse_args()
    if any(cap<1 for cap in args.cutoffs):parser.error('Every cutoff must be positive.')
    output=r.prepare_output(args,parser,['refined-guards-summary.json'])
    if output is None:return
    caps=list(dict.fromkeys(args.cutoffs))
    out=[]
    for cap in caps:
        high=1<<(cap+1);allmask=(high<<1)-1
        def advance(v,op,k,zero):
            if op=='CD' and not(v[k]&(1 if zero else allmask-1)):return None
            w=list(v)
            if op=='CI':w[k]=((v[k]<<1)&allmask)|(v[k]&high)
            if op=='CD':w[k]=1 if zero else ((v[k]&~1)>>1)|(v[k]&high)
            return tuple(w)
        r.advance=advance
        began=time.monotonic();result=r.run((allmask,1,1,allmask,allmask,1,allmask,allmask,allmask))
        record=dict(cap=cap,seconds=time.monotonic()-began,**result)
        print({k:v for k,v in record.items() if k not in ('allowed','rejected','invariants')},flush=True)
        print(record['rejected'],flush=True)
        # Only the compact diagnostic summary is retained; every invariant is
        # rechecked in memory and unchanged exclusions do not warrant bulky copies.
        out.append({k:v for k,v in record.items() if k not in ('allowed','invariants')})
    r.write_json(output/'refined-guards-summary.json',out)

if __name__=='__main__':main()
