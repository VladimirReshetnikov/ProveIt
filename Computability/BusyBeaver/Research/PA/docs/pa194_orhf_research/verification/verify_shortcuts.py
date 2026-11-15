#!/usr/bin/env python3
"""Check the complete finite local certificate for the simultaneous F shortcuts.

The logical proof interpreting this finite certificate in iPRA is in
shortcut_stuttering.tex. This is not a proof of the absolute PA calibration.
"""
from pathlib import Path
import argparse, hashlib, itertools, json
HALT = 254
PATCH = {(26,1):(1,1,91), (101,0):(0,1,17)}
EXPECTED_OLD = {(26,1):(1,1,42), (101,0):(0,-1,26)}
EXPECTED_INCOMING = {
  11: {(14,0,0,-1),(38,0,0,1),(39,0,0,-1),(56,0,0,-1)},
  101: {(96,0,0,1)},
  26: {(11,0,0,-1),(101,0,0,-1)},
}

def need(p, message):
    if not p: raise AssertionError(message)

def read(path):
    rows={}
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'): continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        need((q,b) not in rows, 'duplicate row')
        need(b in (0,1) and w in (0,1) and d in ('L','R'), 'bad row')
        rows[q,b]=(w,1 if d=='R' else -1,n)
    states={q for q,b in rows}
    need(len(states)==194 and len(rows)==388,'wrong control count')
    need(all((q,b)in rows for q in states for b in (0,1)),'partial table')
    need(HALT not in states and {n for w,d,n in rows.values()}-states=={HALT},'bad halt')
    return rows

def pred(rows,q):
    return {(p,b,w,d) for (p,b),(w,d,n) in rows.items() if n==q}

def invariant(q,t,h=0):
    if q==101:return t[h-1]==0
    if q==11:return t[h-1]==0 or t[h+1]==0
    if q==26:return t[h+1]==0 and (t[h]==0 or t[h+2]==0)
    return True

def step(rows,q,h,t):
    if q==HALT:return q,h,t.copy()
    w,d,n=rows[q,t[h]];u=t.copy();u[h]=w
    return n,h+d,u

def induction_check(rows):
    checked=0
    for q in sorted({q for q,b in rows}):
        for bits in itertools.product((0,1),repeat=7):
            t=dict(zip(range(-3,4),bits))
            if not invariant(q,t):continue
            n,h,u=step(rows,q,0,t)
            need(invariant(n,u,h),f'invariant not inductive at {q,bits}')
            checked+=1
    return checked

def verify(parent):
    for k,v in EXPECTED_OLD.items():need(parent[k]==v,f'wrong old row {k}')
    for q,es in EXPECTED_INCOMING.items():need(pred(parent,q)==es,f'wrong predecessors {q}')
    child=dict(parent);child.update(PATCH)
    for q in (11,101):need(pred(child,q)==EXPECTED_INCOMING[q],f'changed predecessor {q}')
    need(pred(child,26)=={(11,0,0,-1)},'wrong child26 predecessors')
    induction=[induction_check(x) for x in (parent,child)]
    local=[]
    for key in PATCH:
        cases=0
        for bits in itertools.product((0,1),repeat=7):
            t=dict(zip(range(-3,4),bits));q,b=key
            if t[0]!=b or not invariant(q,t):continue
            new=step(child,q,0,t)
            old=(q,0,t)
            controls=[q]
            for _ in range(3):
                old=step(parent,*old);controls.append(old[0]);need(old[0]!=HALT,'hidden halt')
            need(new==old,f'endpoint mismatch at {key,bits}')
            cases+=1
        local.append(dict(row=key,valid_local_assignments=cases,parent_steps=3,child_steps=1))
    need(sum(parent[k]!=child[k] for k in parent)==2,'unexpected mutation')
    return child,dict(parent_inductive_local_cases=induction[0],child_inductive_local_cases=induction[1],
        shortcuts=local,ordinary_rows=386,all_exterior_cells_unread=True,
        duration='1 + 2 * shortcut_indicator',cumulative_clock='n + 2 * sum(j<n, shortcut_indicator(new_run(j)))',
        scope='Exact finite local equations and inductive invariant; interpreted by the accompanying written iPRA proof.')

def main():
    a=argparse.ArgumentParser();a.add_argument('--orh',required=True,type=Path);a.add_argument('--orhb',required=True,type=Path)
    a.add_argument('--orhf',type=Path);a.add_argument('--orhbf',type=Path);a.add_argument('--output',required=True,type=Path)
    x=a.parse_args();result={}
    parents=[]
    for name,p,c in [('PA194ORHF',x.orh,x.orhf),('PA194ORHBF',x.orhb,x.orhbf)]:
        old=read(p);parents.append(old);new,r=verify(old)
        if c is not None:need(read(c)==new,f'provided {name} differs')
        r.update(parent_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),supplied_child_checked=c is not None)
        result[name]=r
    diff={k:(parents[0][k],parents[1][k])for k in parents[0]if parents[0][k]!=parents[1][k]}
    expected_b={(87,0):((0,1,301),(0,1,88)),(88,0):((0,1,122),(0,-1,301)),
      (301,0):((0,1,45),(0,1,122)),(301,1):((1,1,103),(1,1,301))}
    need(diff==expected_b,'ORHB is not the exact stated B composition')
    result['B_compatibility']=dict(changed_rows=4,all_disjoint_from_shortcut_states=True,
      all_exceptional_incoming_sets_unchanged=True)
    x.output.parent.mkdir(parents=True,exist_ok=True);x.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
