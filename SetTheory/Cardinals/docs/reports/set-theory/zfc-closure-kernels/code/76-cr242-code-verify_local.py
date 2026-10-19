#!/usr/bin/env python3
"""Independent finite proof checker for whole-tape positive-block equivalence.

Every traced read must lie in the given finite context. Thus all unmentioned
tape cells are universally quantified and preserved, rather than set to zero.
This program checks the finite lemmas; the induction theorem is in report.tex.
It imports no search, register-machine, source-decoder, or symbolic-box code.
"""
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parents[1]
BASE_SHA='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
START,HALT=95,254
INTERNAL={15,27}
FORCED={18,47,65}
MACROS={(11,0),(18,0),(47,0),(65,0)}

def read(path):
    table={};start=None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
            assert (q,b) not in table and b in (0,1) and w in (0,1) and d in ('L','R')
            table[q,b]=w,d,t
    states={q for q,b in table}
    assert start==START and set(table)=={(q,b) for q in states for b in (0,1)}
    assert {t for w,d,t in table.values()}-states=={HALT}
    return table,states

def incoming(table,target):
    return sorted((q,b,w,d) for (q,b),(w,d,t) in table.items() if t==target)

def run(table,q,context,ticks):
    head=0;tape=dict(context);trace=[]
    for _ in range(ticks):
        assert head in tape, ('Unfixed exterior read',q,head)
        assert q!=HALT
        b=tape[head];w,d,n=table[q,b]
        trace.append([q,head,b,w,d,n])
        tape[head]=w;head+=1 if d=='R' else -1;q=n
    return (q,head,tape),trace

def main():
    if not __debug__: raise RuntimeError('Run with Python assertions enabled.')
    bp=ROOT/'reference/zfc_combined243_old.tm';np=ROOT/'machine/zfc_context242_old.tm'
    assert hashlib.sha256(bp.read_bytes()).hexdigest()==BASE_SHA
    old,os=read(bp);new,ns=read(np)
    assert len(os)==243 and len(ns)==242 and ns==os-{15}
    delta={k:v for k,v in new.items() if old[k]!=v}
    assert delta=={(11,0):(0,'R',27),(27,1):(1,'R',22)}
    assert set(old)-set(new)=={(15,0),(15,1)}
    # Old invariant: q in FORCED => T[h-1]=0; q=27 => T[h]=0.
    # Every incoming transition to a FORCED state writes 0 and moves R.
    forcing={q:incoming(old,q) for q in sorted(FORCED)}
    for q,rows in forcing.items():
        assert rows and all((w,d)==(0,'R') for _,_,w,d in rows)
    assert incoming(old,27)==[(18,0,0,'L'),(47,0,0,'L'),(65,0,0,'L')]
    assert incoming(old,15)==[(11,0,0,'R')]
    assert START not in FORCED|INTERNAL
    # Closure of all ordinary comparison boundaries, including halting edges.
    ordinary=[]
    for q in sorted(os-INTERNAL):
        for b in (0,1):
            if (q,b) in MACROS: continue
            assert old[q,b]==new[q,b] and old[q,b][2] not in INTERNAL
            ordinary.append([q,b])
    for table in (old,new):
        for (q,b),(w,d,t) in table.items():
            if q not in INTERNAL and t in INTERNAL:
                assert (q,b) in MACROS
    specs=[('reuse-zero',11,{0:0,1:0},2,4,21,2),
           ('reuse-one',11,{0:0,1:1},2,2,22,2)]
    specs += [(f'old-entry-{q}',q,{-1:0,0:0},2,2,32,-2) for q in sorted(FORCED)]
    cases=[];covered=set()
    for name,q,ctx,a,b,endq,endh in specs:
        left,lt=run(old,q,ctx,a);right,rt=run(new,q,ctx,b)
        assert left==right==(endq,endh,ctx)
        assert endq not in INTERNAL|FORCED and 0<a<=b<=2*a
        covered.add((q,ctx[0]))
        cases.append(dict(name=name,entry=q,context=ctx,old_steps=a,new_steps=b,
            target=endq,head_displacement=endh,old_trace=lt,new_trace=rt,
            no_exterior_read=True,whole_tape_equal=True))
    assert covered==MACROS
    # Each macro row is partitioned by all binary values not fixed by the invariant.
    assert [s[2][1] for s in specs if s[1]==11]==[0,1]
    assert all(s[2]=={-1:0,0:0} for s in specs if s[1] in FORCED)
    canonical=ROOT/'machine/zfc_context242.tm'
    cm={};canonical_start=None
    for line in canonical.read_text().splitlines():
        if line.startswith('#! start '):
            assert canonical_start is None
            canonical_start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,t=line.split();cm[int(q),int(b)]=(int(w),d,int(t))
            # The file is also parsed by the duplicate-rejecting parser below.
    assert canonical_start==0 and len(cm)==484
    seen=set()
    for line in canonical.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();key=int(q),int(b)
            assert key not in seen and int(b) in (0,1) and int(w) in (0,1) and d in ('L','R')
            seen.add(key)
    ren=json.loads((ROOT/'machine/renumbering.json').read_text())
    mp={int(k):v for k,v in ren['old_to_canonical'].items()}
    assert set(mp)==ns|{HALT} and set(mp.values())==set(range(243))
    assert mp[START]==0 and mp[HALT]==242
    assert cm=={(mp[q],b):(w,d,mp[t]) for (q,b),(w,d,t) in new.items()}
    record=dict(status='PASS_INDEPENDENT_LOCAL_PROOF',baseline_sha256=BASE_SHA,
        candidate_sha256=hashlib.sha256(np.read_bytes()).hexdigest(),
        canonical_sha256=hashlib.sha256(canonical.read_bytes()).hexdigest(),
        ordinary_rows=len(ordinary),ordinary_row_list=ordinary,
        invariant_incoming=forcing,local_cases=cases,working_states=242,
        theorem_scope='Same head and arbitrary entire binary tape, initial inherited state95: halting equivalence.',
        conditional_time_bound='If halting, T243 <= T242 <= 2*T243; T242 = T243+2*K.',
        K='Number of paired q11/read0 blocks whose right neighbor is0.',
        proof_assistant_kernel_checked=False)
    out=ROOT/'evidence/independent-local-proof.json'
    out.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ('ordinary_row_list','invariant_incoming','local_cases')},indent=2))

if __name__=='__main__': main()
