"""Verify and materialize the four dedicated-helper pair folds (no state saving).

The invariant audit independently checks initial inclusion and abstract-step
closure of the radius-7 characteristic vector. Each local fold then checks the
complete two-cell context projection against its positive 1-, 3-, or 5-step block.
This is an executable finite certificate check, not a proof-assistant artifact.
"""
from pathlib import Path
import hashlib, json, subprocess, sys
import numpy as np
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
BASE=ROOT/'upstream/U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29/machine'

def read(path):
    t={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();t[int(q),int(b)]=int(w),(1 if d=='R' else -1),int(z)
    return t

def encode(t):
    return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))

def verify_invariant(t,path,rad=7):
    width=2*rad+1;n=1<<width;mask=n-1
    seen=np.frombuffer(path.read_bytes(),dtype=np.uint8).reshape(512,n)
    assert np.all(seen[0]==1)
    count=0
    for q in {q for q,b in t}:
        patterns=np.flatnonzero(seen[q]);count+=len(patterns)
        for bit in (0,1):
            x=patterns[((patterns>>rad)&1)==bit]
            w,d,z=t[q,bit]
            if z==254:continue
            x=(x&~(1<<rad))|(w<<rad)
            if d==1:y=x>>1;edge=1<<(2*rad)
            else:y=(x<<1)&mask;edge=1
            assert np.all(seen[z,y]) and np.all(seen[z,y|edge]),(q,bit)
    return seen,{'radius':rad,'states':len(t)//2,'abstract_configurations':count,
                 'initial_all_tapes':True,'transition_closed':True,
                 'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

receipts=[]
for label,sub,window in [('A','', 'window7.bin'),('B','compatibility_variant','../comparison/double_helper/window7b_history.bin')]:
    base=BASE/sub;t=read(base/'u208.native.tm');seen,invariant=verify_invariant(t,ROOT/'analysis/reduction_search'/window)
    helpers=[list(map(int,line.split()))for line in (OUT/f'helpers_extended_{label}.txt').read_text().splitlines()]
    selected=[];pairs=set()
    for row in helpers:
        key=tuple(sorted(row[:2]))
        if key not in pairs:selected.append(row);pairs.add(key)
    sites=json.loads((base/'sites.json').read_text())
    for drop,keep,changed,x0,x1,w0,w1 in selected:
        pi=lambda q:keep if q==drop else q
        nt={(q,b):(w,d,pi(z))for(q,b),(w,d,z)in t.items()if q!=drop}
        nt[keep,changed]=changed,-1,500
        nt[500,0]=w0,1,pi(x0);nt[500,1]=w1,1,pi(x1)
        two_cells=0
        for q in (drop,keep):
            for bit in (0,1):
                patterns=np.flatnonzero(seen[q]);patterns=patterns[((patterns>>7)&1)==bit]
                for left in set(map(int,(patterns>>6)&1)):
                    two_cells+=1;before={-1:left,0:bit};tape=dict(before);h=0;s=keep
                    w,d,z=t[q,bit];expected=dict(before);expected[0]=w
                    for step in range(1,6):
                        assert h in tape
                        w1,d1,s=nt[s,tape[h]];tape[h]=w1;h+=d1
                        if s==pi(z) and h==d and tape==expected:break
                    else:raise AssertionError((label,drop,keep,changed,q,bit,left))
        d=OUT/f'one_fold_{label}_{drop}_{keep}';d.mkdir(exist_ok=True)
        (d/'machine.native.tm').write_text(encode(nt))
        (d/'sites.tsv').write_text(''.join(f'{p}\t{o}\t{-1 if a is None else a}\n'for p,o,a in sites))
        check=subprocess.run([str(ROOT/'analysis/comparison/finite_fast'),str(d/'machine.native.tm'),str(d/'sites.tsv')],capture_output=True,text=True)
        receipt={'class':label,'fold':[drop,keep,changed],'helper_rows':[nt[500,0],nt[500,1]],'states':len(nt)//2,
                 'local_blocks':'all two-cell projections verified in 1, 3 or 5 steps','two_cell_cases':two_cells,
                 'invariant':invariant,'finite_checker_passed':check.returncode==0,'finite_checker_output':check.stdout+check.stderr}
        (d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');receipts.append(receipt)
        print(json.dumps(receipt),flush=True)
(OUT/'verified_helpers.json').write_text(json.dumps(receipts,indent=2)+'\n')
