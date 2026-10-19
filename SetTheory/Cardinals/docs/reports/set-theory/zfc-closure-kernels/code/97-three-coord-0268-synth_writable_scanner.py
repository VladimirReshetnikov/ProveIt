#!/usr/bin/env python3
"""Bounded synthesis of a restoring zero-run scanner (discovery, not a proof).

Seven working states replace the eight-state read-only detector.  State 0
preserves and skips a 1 to the left.  From the rightmost zero of a run of k
zeros, k=1,...,7, return to state 0 immediately left of the left boundary 1, restoring every
cell.  Eight zeros must enter exit state 7 at displacement -8, also restoring
every cell.  Head motion is limited to the run and its right boundary.
The bounded input restriction permits later universal composition by run
induction if a table is found and independently checked.
"""
from pathlib import Path
import argparse, json, time
import z3

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--states',type=int,default=7)
    ap.add_argument('--horizon',type=int,default=32)
    ap.add_argument('--control',action='store_true')
    ap.add_argument('--readonly',action='store_true')
    ap.add_argument('--bfs-symmetry',action='store_true')
    ap.add_argument('--reset-read1-prefix',type=int,default=0)
    ap.add_argument('--first-write',type=int,choices=(0,1),default=None)
    ap.add_argument('--first-left',action='store_true')
    ap.add_argument('--timeout',type=int,default=300000)
    ap.add_argument('--output',type=Path,default=Path('scanner-synthesis.json'))
    args=ap.parse_args(); n=args.states; H=args.horizon
    if n < 2 or H < 1 or not 0 <= args.reset_read1_prefix < n:
        ap.error('Require states >= 2, horizon >= 1, and 0 <= reset-read1-prefix < states.')
    QW=n.bit_length(); W=11
    s=z3.Solver(); s.set(timeout=args.timeout)
    rows=[]
    for q in range(n):
        row=[]
        for b in range(2):
            w=z3.Bool(f'w_{q}_{b}'); d=z3.Bool(f'right_{q}_{b}'); t=z3.BitVec(f'target_{q}_{b}',QW)
            s.add(z3.ULE(t,n));row.append((w,d,t))
        rows.append(row)
    s.add(rows[0][1][0], z3.Not(rows[0][1][1]), rows[0][1][2]==0)
    s.add(rows[0][0][2]==1)
    if args.first_write is not None:s.add(rows[0][0][0]==bool(args.first_write))
    if args.first_left:s.add(z3.Not(rows[0][0][1]))
    if args.readonly:
        for qi in range(n):
            for bi in range(2):s.add(rows[qi][bi][0]==bool(bi),z3.Not(rows[qi][bi][1]))
    if args.control:
        assert n==8
        for qi in range(n):
            s.add(z3.Not(rows[qi][0][0]), z3.Not(rows[qi][0][1]), rows[qi][0][2]==qi+1)
            s.add(rows[qi][1][0],z3.Not(rows[qi][1][1]),rows[qi][1][2]==0)
    for qi in range(1,args.reset_read1_prefix+1):
        s.add(rows[qi][1][0],z3.Not(rows[qi][1][1]),rows[qi][1][2]==0)
    if args.bfs_symmetry:
        greatest=z3.BitVecVal(0,QW)
        for qi in range(n):
            s.add(z3.UGE(greatest,qi))
            for bi in (0,1):
                target=rows[qi][bi][2]
                s.add(z3.Or(target==n,z3.ULE(target,greatest+1)))
                greatest=z3.If(z3.And(target!=n,z3.UGT(target,greatest)),target,greatest)
    traces=[]
    for k in range(1,9):
        init=(1<<10) | ((1<<(9-k)) if k<8 else 0)
        endhead=8-k if k<8 else 1
        q=z3.BitVec(f'q{k}_0',QW);h=z3.BitVec(f'h{k}_0',4);t=z3.BitVec(f'tape{k}_0',W)
        s.add(q==0,h==9,t==init)
        for j in range(H):
            goal=z3.And(q==(0 if k<8 else n),h==endhead,t==init)
            q2=z3.BitVec(f'q{k}_{j+1}',QW);h2=z3.BitVec(f'h{k}_{j+1}',4);t2=z3.BitVec(f'tape{k}_{j+1}',W)
            s.add(z3.UGE(h,endhead),z3.ULE(h,10),z3.Implies(h==endhead,goal),z3.ULE(q,n))
            if k<8:s.add(q!=n)
            else:s.add(z3.Implies(q==n,goal))
            b=z3.Extract(0,0,z3.LShR(t,z3.ZeroExt(W-4,h)))==1
            writes=[];rights=[];targets=[]
            for qi in range(n):
                writes.append(z3.And(q==qi,z3.If(b,rows[qi][1][0],rows[qi][0][0])))
                rights.append(z3.And(q==qi,z3.If(b,rows[qi][1][1],rows[qi][0][1])))
                targets.append((q==qi,z3.If(b,rows[qi][1][2],rows[qi][0][2])))
            w=z3.Or(writes);d=z3.Or(rights)
            nq=z3.BitVecVal(n,QW)
            for cond,val in reversed(targets):nq=z3.If(cond,val,nq)
            mask=z3.BitVecVal(1,W)<<z3.ZeroExt(W-4,h)
            nt=z3.If(w,t|mask,t&~mask)
            s.add(q2==z3.If(goal,q,nq),h2==z3.If(goal,h,z3.If(d,h+1,h-1)),t2==z3.If(goal,t,nt))
            q,h,t=q2,h2,t2
        s.add(q==(0 if k<8 else n),h==endhead,t==init)
        traces.append(k)
    began=time.monotonic();res=s.check(); elapsed=time.monotonic()-began
    output=dict(status=str(res),states=n,horizon=H,seconds=elapsed,timeout_ms=args.timeout,
      tested_run_lengths=traces,control=args.control,readonly=args.readonly,bfs_symmetry=args.bfs_symmetry,reset_read1_prefix=args.reset_read1_prefix,first_write=args.first_write,first_left=args.first_left,scope='Bounded synthesis on a restrictive restoring block interface; no lower bound for general scanners.')
    if res==z3.sat:
        m=s.model();output['rows']=[[q,b,int(z3.is_true(m.eval(w))), 'R' if z3.is_true(m.eval(d)) else 'L',m.eval(t).as_long()]
            for q in range(n)for b,(w,d,t)in enumerate(rows[q])]
    elif res==z3.unknown:output['reason']=s.reason_unknown()
    args.output.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2),flush=True)

if __name__=='__main__':main()
