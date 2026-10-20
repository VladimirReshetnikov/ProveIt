#!/usr/bin/env python3
"""Bounded CEGIS for merging two roles and rewriting a retained helper.

All four rows of the merged state and retained helper are unknown.  Each old
context must reach a positive original-trajectory endpoint, before reading past
its supplied window.  The window cover is a premise, not proved by this search.
Successful models are proposals requiring independent replay and fresh startup.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'machine218/vendor_z3'))
import z3


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table', type=Path)
    ap.add_argument('windows', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--keep', type=int, default=40)
    ap.add_argument('--drop', type=int, default=302)
    ap.add_argument('--helper', type=int, default=54)
    ap.add_argument('--radius', type=int, default=7)
    ap.add_argument('--bound', type=int, default=12)
    ap.add_argument('--old-bound', type=int, default=25)
    ap.add_argument('--query-ms', type=int, default=30000)
    ap.add_argument('--seconds', type=int, default=240)
    ap.add_argument('--counterexamples', type=int, default=4)
    ap.add_argument('--fix-common', action='store_true')
    a = ap.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    table = {}
    for line in a.table.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,z = line.split()
            table[int(q),int(b)] = int(w), 1 if d=='R' else -1, int(z)
    native = sorted({q for q,b in table})
    assert len(native) < 255 and 254 not in native
    mapping = {q:i for i,q in enumerate(native+[254])}
    keep,drop,helper,halt = [mapping[q] for q in (a.keep,a.drop,a.helper,254)]
    red = lambda q: keep if q==drop else q
    T = {(mapping[q],b):(w,d,mapping[z]) for (q,b),(w,d,z) in table.items()}
    TT = {(q,b):(w,d,red(z)) for (q,b),(w,d,z) in T.items()}
    N,center = 2*a.radius+1,a.radius
    assert N < 32
    tape_width = 32
    head_width = 6
    cases = []
    for line in a.windows.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,x = map(int,line.split())
        if q not in (a.keep,a.drop,a.helper):continue
        assert 0 <= x < 1<<N
        oq,h,t = mapping[q],center,x
        goals = []
        for _ in range(a.old_bound):
            if not 0<=h<N or oq==halt:break
            w,d,z = T[oq,(t>>h)&1]
            t = (t & ~(1<<h)) | (w<<h)
            h += d
            oq = z
            goals.append((red(oq),h,t))
        assert goals
        cases.append((mapping[q],x,tuple(goals)))
    assert all(any(c[0]==q for c in cases) for q in (keep,drop,helper))
    started = time.monotonic()
    solver = z3.SolverFor('QF_AUFBV')
    solver.set(timeout=a.query_ms)
    action_width = 10
    rows = {(q,b):z3.BitVec(f'row_{native[q]}_{b}',action_width)
            for q in (keep,helper) for b in (0,1)}
    for action in rows.values():
        target = z3.Extract(9,2,action)
        solver.add(z3.ULT(target,len(native)+1),target!=drop)
    if a.fix_common:
        for b in (0,1):
            if TT[keep,b] == TT[drop,b]:
                w,d,z = TT[keep,b]
                solver.add(rows[keep,b] == (z<<2) | (int(d==1)<<1) | w)
    known = z3.K(z3.BitVecSort(9),z3.BitVecVal(0,action_width))
    for (q,b),(w,d,z) in TT.items():
        known = z3.Store(known,z3.BitVecVal((q<<1)|b,9),
                         z3.BitVecVal((z<<2)|(int(d==1)<<1)|w,action_width))
    # Simplification leaves a shared immutable lookup expression across cases.
    known = z3.simplify(known)
    constraints = set()
    def constrain(index):
        if index in constraints:return
        constraints.add(index)
        oq,x,goals = cases[index]
        q,h,t = z3.BitVecVal(red(oq),8),z3.BitVecVal(center,head_width),z3.BitVecVal(x,tape_width)
        done = z3.BoolVal(False)
        for n in range(a.bound):
            solver.add(z3.Implies(z3.Not(done),z3.And(z3.ULT(h,N),q!=halt)))
            sh = z3.ZeroExt(tape_width-head_width,h)
            bit = z3.Extract(0,0,z3.LShR(t,sh))
            action = z3.If(q==keep,z3.If(bit==0,rows[keep,0],rows[keep,1]),
                     z3.If(q==helper,z3.If(bit==0,rows[helper,0],rows[helper,1]),
                           z3.Select(known,z3.Concat(q,bit))))
            nq = z3.Extract(9,2,action)
            nh = h + z3.If(z3.Extract(1,1,action)==1,
                          z3.BitVecVal(1,head_width),z3.BitVecVal(-1,head_width))
            mask = z3.BitVecVal(1,tape_width)<<sh
            nt = (t & ~mask) | (z3.ZeroExt(tape_width-1,z3.Extract(0,0,action))<<sh)
            # Name intermediate states to avoid expression-tree expansion.
            qq = z3.BitVec(f'q_{index}_{n}',8)
            hh = z3.BitVec(f'h_{index}_{n}',head_width)
            tt = z3.BitVec(f't_{index}_{n}',tape_width)
            dd = z3.Bool(f'done_{index}_{n}')
            solver.add(qq==z3.If(done,q,nq),hh==z3.If(done,h,nh),tt==z3.If(done,t,nt))
            terms = [qq==halt if gq==halt else
                     z3.And(qq==gq,hh==gh,tt==gt) for gq,gh,gt in goals]
            solver.add(dd==z3.Or(done,*terms))
            q,h,t,done = qq,hh,tt,dd
        solver.add(done)

    def decode(model):
        patch = {}
        for key,row in rows.items():
            action = model.eval(row,model_completion=True).as_long()
            patch[key] = action&1,1 if action&2 else -1,action>>2
        return patch

    def verify(patch,index):
        oq,x,goals = cases[index]
        q,h,t = red(oq),center,x
        for n in range(a.bound):
            if not 0<=h<N or q==halt:return False
            row = patch.get((q,(t>>h)&1),TT[q,(t>>h)&1])
            w,d,z = row
            t = (t & ~(1<<h)) | (w<<h)
            h += d
            q = z
            if any((q==halt and gq==halt) or (q,h,t)==(gq,gh,gt) for gq,gh,gt in goals):return True
        return False

    # Include each role and scanned-symbol class, retaining the actual full
    # window for the eventual independent exhaustive finite check.
    seeded = set()
    for i,(q,x,goals) in enumerate(cases):
        key = q,(x>>center)&1
        if key not in seeded:
            constrain(i)
            seeded.add(key)
    iterations = []
    status = 'TIME_LIMIT'
    hit = None
    while time.monotonic()-started < a.seconds:
        begin = time.monotonic()
        answer = solver.check()
        row = dict(iteration=len(iterations)+1,answer=str(answer),seconds=time.monotonic()-begin,
                   constrained_cases=len(constraints))
        if answer==z3.unsat:
            iterations.append(row)
            status='BOUNDED_FAMILY_UNSAT'
            break
        if answer!=z3.sat:
            row['reason']=solver.reason_unknown()
            iterations.append(row)
            status='SOLVER_UNKNOWN'
            break
        patch = decode(solver.model())
        bad = [i for i in range(len(cases)) if not verify(patch,i)]
        row.update(failing_cases=len(bad),patch={f'{native[q]}/{b}':[w,d,(native+[254])[z]]
                                               for (q,b),(w,d,z) in patch.items()})
        iterations.append(row)
        print(json.dumps(row),flush=True)
        if not bad:
            hit=row['patch']
            status='FINITE_CONTEXT_CANDIDATE'
            break
        unseen = [i for i in bad if i not in constraints]
        assert unseen, 'SMT/concrete semantic disagreement'
        # Spread counterexamples over old-role/scanned-symbol classes first.
        picked=[]
        groups=set()
        for i in unseen:
            q,x,_=cases[i]
            g=q,(x>>center)&1
            if g not in groups:
                picked.append(i);groups.add(g)
        for i in unseen:
            if len(picked)>=a.counterexamples:break
            if i not in picked:picked.append(i)
        for i in picked[:a.counterexamples]:constrain(i)
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    receipt=dict(status=status,keep=a.keep,drop=a.drop,helper=a.helper,radius=a.radius,
                 new_bound=a.bound,old_bound=a.old_bound,cases=len(cases),
                 all_four_rows_unknown=not a.fix_common,constrained_cases=len(constraints),
                 iterations=iterations,seconds=time.monotonic()-started,hit=hit,
                 table_sha256=sha(a.table),windows_sha256=sha(a.windows),source_sha256=sha(Path(__file__)),
                 proof_boundary='Bounded solver family only. Supplied window coverage is a premise; post-init results require a separate blank startup proof. A candidate must be independently replayed.')
    (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)


if __name__=='__main__':
    main()
