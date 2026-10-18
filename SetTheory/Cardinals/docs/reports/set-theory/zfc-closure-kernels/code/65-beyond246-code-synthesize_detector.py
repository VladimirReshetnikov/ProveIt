#!/usr/bin/env python3
"""Bounded synthesis of a tape-restoring nine-zero recognizer with fewer states.

Temporary writes and two-way excursions are permitted inside the known window.
An UNSAT result applies only to the explicit step/window bound.
"""
from pathlib import Path
import sys,time,argparse,json
import z3 as z

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--states',type=int,default=8);ap.add_argument('--steps',type=int,default=40);ap.add_argument('--seconds',type=int,default=90);args=ap.parse_args()
    n=args.states;assert 3<=n<=14
    S=z.SolverFor('QF_BV');S.set(timeout=args.seconds*1000)
    W=[z.BitVec(f'w_{q}_{b}',1) for q in range(n) for b in range(2)]
    D=[z.Bool(f'right_{q}_{b}') for q in range(n) for b in range(2)]
    N=[z.BitVec(f'next_{q}_{b}',4) for q in range(n) for b in range(2)]
    for x in N:S.add(z.ULE(x,n))
    # Preserve the two register-marking transitions and one-run scan.
    S.add(W[0]==0,z.Not(D[0]),N[0]==1)
    S.add(W[1]==1,z.Not(D[1]),N[1]==0)
    S.add(W[3]==1,z.Not(D[3]),N[3]==0)
    # Fix no other transition. Every nonstart state may be reached by an
    # earlier-index state's edge after a suitable breadth-first renumbering.
    for q in range(1,n):
        S.add(z.Or([N[k]==q for k in range(2*q)]))
    def choose(vec,q,b):
        a=vec[-1]
        for j in range(len(vec)-2,-1,-1):
            a=z.If(z.And(q==j//2,b==j%2),vec[j],a)
        return a
    vars=[]
    for r in range(10):
        initial=(1<<10)|((1<<(9-r)) if r<9 else 0)
        low=9-r if r<9 else 1
        Q=[z.BitVec(f'q_{r}_{t}',4) for t in range(args.steps+1)]
        H=[z.BitVec(f'h_{r}_{t}',5) for t in range(args.steps+1)]
        T=[z.BitVec(f'tape_{r}_{t}',11) for t in range(args.steps+1)]
        S.add(Q[0]==0,H[0]==9,T[0]==initial)
        def finished(t):
            return z.And(Q[t]==(0 if r<9 else n),H[t]==(8-r if r<9 else 0),T[t]==initial)
        for t in range(args.steps):
            active=z.Not(finished(t))
            S.add(z.Implies(active,z.And(z.ULT(Q[t],n),z.UGE(H[t],low),z.ULE(H[t],10))))
            h=z.ZeroExt(6,H[t]);bit=z.Extract(0,0,z.LShR(T[t],h))
            w=choose(W,Q[t],bit);d=choose(D,Q[t],bit);q=choose(N,Q[t],bit)
            written=(T[t]&~(z.BitVecVal(1,11)<<h))|(z.ZeroExt(10,w)<<h)
            S.add(Q[t+1]==z.If(active,q,Q[t]))
            S.add(H[t+1]==z.If(active,z.If(d,H[t]+1,H[t]-1),H[t]))
            S.add(T[t+1]==z.If(active,written,T[t]))
        S.add(finished(args.steps));vars.append((Q,H,T,initial))
    began=time.monotonic();print('Solving',n,'states',args.steps,'steps; constraints',len(S.assertions()),flush=True)
    status=S.check();result=dict(status=str(status),states=n,steps=args.steps,seconds=time.monotonic()-began,timeout_seconds=args.seconds,scope='Bounded local synthesis; SAT needs explicit universal-composition review; UNSAT is not a state lower bound.')
    if status==z.sat:
        m=S.model();rows=[]
        for q in range(n):
            for b in (0,1):
                j=2*q+b;rows.append([q,b,m.eval(W[j],model_completion=True).as_long(),'R' if z.is_true(m.eval(D[j],model_completion=True)) else 'L',m.eval(N[j],model_completion=True).as_long()])
        result['rows']=rows
        result['traces']=[[[m.eval(Q[t],model_completion=True).as_long(),m.eval(H[t],model_completion=True).as_long()-9,m.eval(T[t],model_completion=True).as_long()] for t in range(args.steps+1)] for Q,H,T,initial in vars]
    if status==z.unknown:result['reason_unknown']=S.reason_unknown()
    out=Path(__file__).resolve().parents[1]/'experiments/detector_search';out.mkdir(exist_ok=True)
    (out/f'result-{n}-{args.steps}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='traces'},indent=2),flush=True)
if __name__=='__main__':main()
