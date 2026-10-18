#!/usr/bin/env python3
"""Bounded synthesis of a nondestructive blank-run detector.

Replaces the eight-state suffix of the 246-state return detector.
Every finite positive/negative result is explicitly bounded.
"""
import argparse, json, sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'vendor'))
import z3

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--states',type=int,default=7)
    ap.add_argument('--steps',type=int,default=40)
    ap.add_argument('--seconds',type=int,default=180)
    ap.add_argument('--first-write',type=int,choices=[0,1])
    a=ap.parse_args()
    n=a.states; S=z3.Solver(); S.set(timeout=1000*a.seconds)
    W=[z3.Bool('w%d'%i) for i in range(2*n)]
    D=[z3.Bool('r%d'%i) for i in range(2*n)]
    Q=[z3.BitVec('q%d'%i,4) for i in range(2*n)]
    for q in Q:S.add(z3.ULE(q,n+1))
    # The already-seen one is never modified in the zero-length case.
    S.add(W[1],z3.Not(D[1]),Q[1]==n)
    if a.first_write is not None:S.add(W[0]==bool(a.first_write))
    # Relabeling symmetry: first fresh state is1. Exits are not fresh states.
    S.add(z3.Or(z3.ULE(Q[0],1),z3.UGE(Q[0],n)))
    for j in range(1,n):
        for b in (0,1):S.add(z3.Or(z3.ULE(Q[2*j+b],min(n-1,2*j+1)),z3.UGE(Q[2*j+b],n)))
    def lookup(xs,idx):
        value=xs[-1]
        for i in range(len(xs)-2,-1,-1):value=z3.If(idx==i,xs[i],value)
        return value
    for case in range(9):
        short=case<8; k=case
        initial=(1<<18)|((1<<(16-k)) if short else 0)
        qs=[z3.BitVec(f's{case}_{i}',4) for i in range(a.steps+1)]
        hs=[z3.BitVec(f'h{case}_{i}',5) for i in range(a.steps+1)]
        ts=[z3.BitVec(f't{case}_{i}',32) for i in range(a.steps+1)]
        S.add(qs[0]==0,hs[0]==16,ts[0]==initial)
        for i in range(a.steps):
            active=z3.ULT(qs[i],n)
            S.add(z3.Implies(active,z3.And(z3.ULE(hs[i],18),z3.UGE(hs[i],16-k if short else 0))))
            bit=z3.Extract(0,0,z3.LShR(ts[i],z3.ZeroExt(27,hs[i])))
            index=z3.ZeroExt(1,qs[i])*2+z3.ZeroExt(4,bit)
            write=lookup(W,index); right=lookup(D,index); target=lookup(Q,index)
            mask=z3.BitVecVal(1,32)<<z3.ZeroExt(27,hs[i])
            changed=z3.If(write,ts[i]|mask,ts[i]&~mask)
            S.add(qs[i+1]==z3.If(active,target,qs[i]))
            S.add(hs[i+1]==z3.If(active,z3.If(right,hs[i]+1,hs[i]-1),hs[i]))
            S.add(ts[i+1]==z3.If(active,changed,ts[i]))
        S.add(ts[-1]==initial,qs[-1]==(n if short else n+1))
        if short:S.add(hs[-1]==15-k)
        else:S.add(z3.ULE(hs[-1],17))
    began=time.monotonic(); ans=S.check()
    record={'status':str(ans),'states':n,'step_bound':a.steps,'seconds':time.monotonic()-began,
            'scope':'Nine bounded traces with no read past the first left one; long case has blank left exterior.',
            'first_write':a.first_write}
    if ans==z3.sat:
        m=S.model();table=[]
        for i in range(2*n):
            table.append([i//2,i%2,int(z3.is_true(m.eval(W[i],model_completion=True))),'R' if z3.is_true(m.eval(D[i],model_completion=True)) else 'L',m.eval(Q[i],model_completion=True).as_long()])
        record['table']=table
    elif ans==z3.unknown:record['reason']=S.reason_unknown()
    out=Path(__file__).resolve().parent/f'result_n{n}_t{a.steps}_w{a.first_write}.json'
    out.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2),flush=True)

if __name__=='__main__':main()
