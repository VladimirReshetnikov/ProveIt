#!/usr/bin/env python3
"""Exact bounded nondestructive zero-run detector synthesis using finite CNF.

This is a research search, not an impossibility decision. A SAT answer is
independently replayed on all nine local input classes. Opaque tape is never
read. UNSAT concerns only the explicit bounds and optional restrictions.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, threading, time
from pathlib import Path

if Path('/tmp/zfc246-solvers').exists():
    sys.path.insert(0, '/tmp/zfc246-solvers')
from pysat.solvers import Solver
from pysat.formula import IDPool


class Encoder:
    def __init__(self, n, steps, exact, first, one, nowrite=False):
        self.n, self.steps, self.exact = n, steps, exact
        self.pool, self.cnf = IDPool(), []
        self.done = []
        self.w = [self.v(('w', i)) for i in range(2*n)]
        self.d = [self.v(('d', i)) for i in range(2*n)]
        self.q = [[self.v(('q', i, j)) for j in range(n+2)] for i in range(2*n)]
        for row in self.q:
            self.onehot(row)
        if first != 'free':
            self.add([self.w[0] if first[0] == '1' else -self.w[0]])
            self.add([self.d[0] if first[1] == 'R' else -self.d[0]])
            self.add([self.q[0][1]])
        if one:
            self.add([self.w[1]])
            self.add([-self.d[1]])
            self.add([self.q[1][n]])
        if nowrite:
            for i in range(2*n):
                self.add([self.w[i] if i % 2 else -self.w[i]])

    def v(self, key): return self.pool.id(key)
    def add(self, clause): self.cnf.append(clause)
    def eq(self, a, b, cond=()):
        pre = [-c for c in cond]
        self.add(pre + [-a,b]); self.add(pre + [a,-b])
    def onehot(self, vs):
        self.add(list(vs))
        for i,a in enumerate(vs):
            for b in vs[i+1:]: self.add([-a,-b])

    def case(self, k):
        if k in self.done: return
        self.done.append(k)
        n,T = self.n,self.steps
        lo,hi = (-k if k<8 else -7),2
        ps = list(range(lo-1,hi+2))
        cells = list(range(lo,hi+1))
        initial = {2} | ({-k} if k<8 else set())
        s = [[self.v((k,'s',t,q)) for q in range(n+2)] for t in range(T+1)]
        h = [{p:self.v((k,'h',t,p)) for p in ps} for t in range(T+1)]
        tape = [{p:self.v((k,'t',t,p)) for p in cells} for t in range(T+1)]
        for t in range(T+1):
            self.onehot(s[t]); self.onehot(list(h[t].values()))
        self.add([s[0][0]]); self.add([h[0][0]])
        for p in cells: self.add([tape[0][p] if p in initial else -tape[0][p]])
        for t in range(T):
            active = self.v((k,'active',t))
            self.add([-active] + s[t][:n])
            for q in range(n): self.add([-s[t][q],active])
            # All active reads are inside the known window, including the
            # first left 1 for short cases. No opaque cell is queried.
            for p in [lo-1,hi+1]: self.add([-active,-h[t][p]])
            read, write, right = [self.v((k,x,t)) for x in ('read','write','right')]
            for p in cells: self.eq(read,tape[t][p],[h[t][p],active])
            for q in range(n):
                for b in range(2):
                    cond = [s[t][q],read if b else -read]
                    row=2*q+b
                    self.eq(write,self.w[row],cond)
                    self.eq(right,self.d[row],cond)
                    for j in range(n+2): self.eq(s[t+1][j],self.q[row][j],cond)
            # Absorbing exits retain every represented cell and the head.
            for q in (n,n+1): self.add([-s[t][q],s[t+1][q]])
            for p in ps:
                self.eq(h[t+1][p],h[t][p],[-active])
                if p in cells:
                    self.add([-active,-h[t][p],-right,h[t+1][p+1]])
                    self.add([-active,-h[t][p],right,h[t+1][p-1]])
                    self.eq(tape[t+1][p],write,[active,h[t][p]])
                    self.eq(tape[t+1][p],tape[t][p],[-h[t][p]])
                    self.eq(tape[t+1][p],tape[t][p],[-active])
        self.add([s[T][n if k<8 else n+1]])
        if k<8:
            self.add([h[T][-k-1]])
        elif self.exact:
            self.add([h[T][-8]])
        else:
            self.add([h[T][p] for p in range(-7,2)])
        for p in cells: self.add([tape[T][p] if p in initial else -tape[T][p]])

    def table(self, model):
        positive=set(v for v in model if v>0)
        return [[i//2,i%2,int(self.w[i] in positive),
                 'R' if self.d[i] in positive else 'L',
                 next(j for j,q in enumerate(self.q[i]) if q in positive)]
                for i in range(2*self.n)]


def replay(table,n,steps,exact):
    rows={(q,b):(w,d,r) for q,b,w,d,r in table}
    records=[]
    for k in range(9):
        lo=-k if k<8 else -7
        initial={2}|({-k} if k<8 else set())
        ones=initial.copy(); q=h=0; trace=[]
        ok=True; reason='fuel'
        for t in range(steps):
            if q>=n: break
            if not lo<=h<=2:
                ok=False; reason='opaque-read'; break
            bit=int(h in ones); w,d,r=rows[q,bit]
            trace.append([q,h,bit,w,d,r])
            if w: ones.add(h)
            else: ones.discard(h)
            q=r; h+=1 if d=='R' else -1
        wanted=n if k<8 else n+1
        valid_head=(h==-k-1 if k<8 else h==-8 if exact else -7<=h<=1)
        passed=ok and q==wanted and valid_head and ones==initial
        records.append(dict(case=k,passed=passed,steps=len(trace),exit_state=q,
                            exit_head=h,ones=sorted(ones),initial=sorted(initial),
                            trace=trace,failure=None if passed else reason))
    return records


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--states',type=int,default=7)
    ap.add_argument('--steps',type=int,default=24)
    ap.add_argument('--seconds',type=float,default=120)
    ap.add_argument('--solver',default='cadical195')
    ap.add_argument('--first',choices=['free','1L','1R','0L','0R'],default='free')
    ap.add_argument('--fixed-one',action='store_true')
    ap.add_argument('--exact',action='store_true')
    ap.add_argument('--no-write',action='store_true')
    ap.add_argument('--cegis',action='store_true')
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args(); began=time.monotonic()
    enc=Encoder(a.states,a.steps,a.exact,a.first,a.fixed_one,a.no_write)
    cases=[0,8] if a.cegis else list(range(9))
    for k in cases: enc.case(k)
    result=dict(configuration=vars(a)|{'output':str(a.output)},status='UNKNOWN',
                scope='Finite exact local contracts with no opaque reads; no global lower bound.',
                rounds=[])
    emitted=0
    with Solver(name=a.solver) as sat:
        while True:
            sat.append_formula(enc.cnf[emitted:]); emitted=len(enc.cnf)
            remaining=a.seconds-(time.monotonic()-began)
            if remaining<=0: break
            timer=threading.Timer(remaining,sat.interrupt)
            timer.start()
            try:
                answer=sat.solve_limited(expect_interrupt=True)
            finally:
                timer.cancel()
            result['rounds'].append(dict(cases=list(enc.done),variables=enc.pool.top,
                                         clauses=emitted,answer=answer,
                                         elapsed=time.monotonic()-began,
                                         statistics=sat.accum_stats()))
            print(json.dumps(result['rounds'][-1]),flush=True)
            if answer is None: break
            if not answer:
                result['status']='UNSAT'; break
            table=enc.table(sat.get_model())
            records=replay(table,a.states,a.steps,a.exact)
            failed=[r['case'] for r in records if not r['passed']]
            if not failed:
                result.update(status='SAT',table=table,replay=records); break
            fresh=[k for k in failed if k not in enc.done]
            if not fresh: raise AssertionError(('SAT encoding replay mismatch',records))
            for k in fresh: enc.case(k)
    result['elapsed']=time.monotonic()-began
    result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('table','replay')},indent=2))

if __name__=='__main__': main()
