#!/usr/bin/env python3
"""Universal binary instruction and register contracts for a pinned candidate.

The run-length engine is the previously reviewed finite-word calculus, with
one explicit nonnegative gap parameter. No finite register bound is used.
This certificate is an ordinary mathematical proof calculation, not a
new Lean/Rocq theorem or a serialized first-order ZFC proof.
"""
from pathlib import Path
import argparse, collections, hashlib, json, sys, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(HERE/'runtime'))
import contracts as c
import colored_affine as affine

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--graph',type=Path,required=True)
    ap.add_argument('--gap',type=int,default=64)
    ap.add_argument('--scanner',type=int,choices=(8,9),default=9)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if not __debug__:ap.error('Assertions must be enabled')
    assert args.gap>=0
    base=ROOT/'vendor/context246'
    review=c.load_module(base/'code/review_affine_source.py','runtime_source_review')
    T=c.read_table(args.table);sites=c.graph_sites(args.graph)
    register=c.register_inductions(base,T)
    if args.scanner==8:scanner=c.scanner_induction(T)
    else:
        chain=c.CHAIN+(74,)
        for i,q in enumerate(chain):
            assert T[str(q),0]==(0,'L',str(chain[i+1] if i+1<len(chain) else 84))
            assert T[str(q),1]==(1,'L','4')
        assert T['84',0]==(0,'R','84') and T['84',1]==(1,'R','96')
        scanner=dict(status='PASS',distinguished_zero_run=9)
    passed=collections.Counter();failures=[];rules=collections.Counter();minimum=10**9
    began=time.monotonic()
    for pc,op,r in sites:
        assert len(pc)<=args.gap
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(r,zero) if op=='CD' else None
            effect=None;extra=0;overflow=False
            if op=='CI':succ,overflow=review.full_inc(pc);effect=('inc',r)
            elif op=='CD' and not zero:succ,overflow=review.full_inc(pc);effect=('dec',r);extra=1
            elif op=='CD':succ,overflow=review.full_inc(review.full_strip(pc,'0',1))
            elif op=='CB':succ,overflow=review.full_inc(review.full_strip(pc,'0',r))
            elif op=='CC':succ=review.full_strip(pc,'1',r)
            else:assert op=='CH';succ=''
            right=[('b',int(b)) for b in succ]+[('r',0,1,args.gap+extra+int(overflow)-len(succ)),('b',1),('box',('plain',effect))]
            try:
                rr,lit=affine.run(T,pc,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=3000,gap=args.gap)
                assert lit>0
                passed[op+('/zero' if zero else '/positive') if op=='CD' else op]+=1
                rules.update(rr);minimum=min(minimum,lit)
            except (AssertionError,KeyError) as e:
                failures.append(dict(pc=pc,op=op,physical_register=r,zero=zero,exception=repr(e)))
    assert sum(passed.values())+len(failures)==8391
    result=dict(status='FAIL' if failures else 'PASS',working_states=len(T)//2,
        table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest(),
        graph_sha256=hashlib.sha256(args.graph.read_bytes()).hexdigest(),
        minimum_header_distance=args.gap,extra_gap='every natural n',
        arbitrary_natural_registers=True,nonempty_arbitrary_spare_suffix=True,
        register_inductions=register,scanner=scanner,universally_verified_cases=sum(passed.values()),
        failures=failures,positive_minimum_literal_steps=minimum,by_operation=dict(passed),
        rule_counts=dict(rules),elapsed_seconds=time.monotonic()-began,
        scope='Universal word and induction certificate; finite symbolic rule limit rejects unresolved cases.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','working_states','universally_verified_cases','minimum_header_distance','positive_minimum_literal_steps')}))
    if failures:print('Rejected cases:',len(failures));return 1
    return 0

if __name__=='__main__':raise SystemExit(main())
