#!/usr/bin/env python3
"""Two independent literal representations, both numberings, entire blank tape."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from construct import load,digest

ROOT=Path(__file__).resolve().parents[1]

def sparse(table,start,ticks,observe=False):
    q,h,ones=start,0,set();extra=0;visited=set()
    for _ in range(ticks):
        if observe and q==11 and h not in ones and h+1 not in ones:extra+=1
        b=int(h in ones);visited.add((q,b));w,d,q=table[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    return (q,h,ones),extra,visited

def dense(table,start,ticks):
    tape=bytearray(2*ticks+3);origin=ticks+1;h=origin;q=start
    for _ in range(ticks):
        w,d,q=table[q,tape[h]];tape[h]=w;h+=1 if d=='R' else -1
    return q,h-origin,{i-origin for i,b in enumerate(tape) if b}

def main():
    if not __debug__: raise RuntimeError('Run with Python assertions enabled.')
    base=ROOT/'reference/zfc_combined243_old.tm'
    candidate=ROOT/'machine/zfc_context242_old.tm'
    canonical=ROOT/'machine/zfc_context242.tm'
    old,start=load(base);new,ns=load(candidate);can,cs=load(canonical)
    assert digest(base)=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
    assert digest(candidate)=='6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0'
    assert len(new)==484 and start==ns==95 and cs==0
    a,k,_=sparse(old,start,407967,True)
    assert a==dense(old,start,407967) and a[0:2]==(96,-5)
    ticks=407967+2*k
    b,_,used=sparse(new,ns,ticks)
    assert b==a==dense(new,ns,ticks)
    c,_,_=sparse(can,cs,ticks)
    assert c==dense(can,cs,ticks)
    mp={int(k):v for k,v in json.loads((ROOT/'machine/renumbering.json').read_text())['old_to_canonical'].items()}
    assert c==(mp[b[0]],b[1],b[2])
    q,h,ones=b;marker=h-1
    assert min(ones)==marker and marker==-6
    header=min(p for p in ones if p>=h);p=header+1;values=[]
    while p<=max(ones):
        assert p not in ones and p+1 in ones
        end=p+1
        while end in ones:end+=1
        values.append(end-p-2);p=end
    assert len(values)>=10
    physical=(6,2,0,4,3,7,8,5,1)
    logical=[values[i] for i in physical]
    assert logical==[3,0,0,0,3,0,0,0,0]
    assert values[9:]==[1]*167 and header==176 and len(ones)==351
    record=dict(status='PASS_INDEPENDENT_BLANK',baseline_ticks=407967,candidate_ticks=ticks,
        slow_blocks=k,old_state=q,canonical_state=mp[q],head=h,marker=marker,header=header,
        span=header-h,logical_registers=logical,spare_values=values[9:],one_count=len(ones),
        all_one_positions=sorted(ones),all_other_cells_zero=True,
        sparse_dense_agreement_both_numberings=True,
        baseline_sha256=digest(base),inherited_sha256=digest(candidate),canonical_sha256=digest(canonical),
        observed_candidate_rows=sorted(used),scope='Finite exact initialization, not a test of nonhalting.')
    (ROOT/'evidence/blank.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ('all_one_positions','spare_values','observed_candidate_rows')},indent=2))

if __name__=='__main__':main()
