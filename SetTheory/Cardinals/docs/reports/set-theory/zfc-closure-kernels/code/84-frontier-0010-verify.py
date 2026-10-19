#!/usr/bin/env python3
"""Independent finite controls. Standard library only; not a nonhalting proof."""
from pathlib import Path
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parents[1]
EXPECTED={
    'zfc_prefix246.tm':'89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc',
    'zfc_prefix246_old.tm':'303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee',
}
def read_table(path):
    start=None; table={}
    for line in path.read_text().splitlines():
        if line.startswith('#! start '): start=int(line.split()[-1])
        if not line.strip() or line.startswith('#'): continue
        q,b,w,d,r=line.split()
        q,b,w,r=map(int,(q,b,w,r))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in table
        table[q,b]=(w,-1 if d=='L' else 1,r)
    assert start is not None
    return start,table

def baseline():
    files={}
    for name,want in EXPECTED.items():
        path=ROOT/'baseline'/name
        got=hashlib.sha256(path.read_bytes()).hexdigest()
        assert got==want,(name,got)
        files[name]=got
    start,T=read_table(ROOT/'baseline/zfc_prefix246.tm')
    old_start,U=read_table(ROOT/'baseline/zfc_prefix246_old.tm')
    rename=json.loads((ROOT/'baseline/renumbering.json').read_text())
    m=rename['canonical_to_old']
    assert len(m)==246 and len(set(m))==246
    mapping=dict(enumerate(m))|{246:254}
    assert start==0 and old_start==95 and mapping[0]==95
    assert set(T)=={(q,b) for q in range(246) for b in (0,1)}
    assert set(U)=={(mapping[q],b) for q in range(246) for b in (0,1)}
    for (q,b),(w,d,r) in T.items():
        assert U[mapping[q],b]==(w,d,mapping[r])
    # Sparse set semantics, separately written from dense loop below.
    ones=set(); q=start; head=0; low=high=0
    for step in range(410735):
        assert q!=246
        w,d,r=T[q,int(head in ones)]
        if w: ones.add(head)
        else: ones.discard(head)
        head+=d; q=r
        low=min(low,head);high=max(high,head)
    assert (q,head)==(88,-5)
    # Dense array semantics with a fixed, checked finite allocation.
    offset=100000
    tape=bytearray(2*offset+1);p=offset;state=start
    for step in range(410735):
        bit=tape[p]
        transition=T[state,bit]
        tape[p]=transition[0]
        p=p+transition[1]
        state=transition[2]
        assert 0<=p<len(tape)
    dense_ones={j-offset for j,bit in enumerate(tape) if bit}
    assert (state,p-offset)==(q,head)
    assert dense_ones==ones
    # Whole endpoint tape: marker, header, primary blocks, finite spare suffix.
    primary=[0,0,0,3,0,0,3,0,0]
    spares=[1]*167
    expected={-6,176}; cursor=177
    for value in primary+spares:
        # B(value) = 0 1^(value+1).
        for x in range(cursor+1,cursor+value+2):expected.add(x)
        cursor+=value+2
    assert expected==ones
    assert len(ones)==351
    # Constants from Permutation252Frame.physOf at the pinned commit.
    logical=[3,0,0,0,3,0,0,0,0]
    logical_to_physical=[6,2,0,4,3,7,8,5,1]
    physical=[None]*9
    for i,j in enumerate(logical_to_physical):physical[j]=logical[i]
    assert physical==primary
    return dict(status='PASS',working_states=246,rows=492,start=0,halt=246,
        steps=410735,state=q,head=head,marker=-6,header=176,gap=181,
        logical_registers=logical,physical_registers=primary,spare_count=167,
        spare_value=1,one_cells=len(ones),full_tape_equality=True,
        sparse_dense_equal=True,visited_head_min=low,visited_head_max=high,
        last_one=max(ones),first_one=min(ones),sha256=files,
        scope='Exact finite initialization and renumbering only; no unbounded runtime or consistency proof.')

def detector_controls():
    records=[]
    for name in ('control8_exact.json','control8_shared_exact.json'):
        result=json.loads((ROOT/'experiments/detector'/name).read_text())
        assert result['status']=='SAT'
        config=result['configuration'];n=config['states'];limit=config['steps']
        shared='borrowed_fixed_states' in result
        table={(q,b):(w,1 if d=='R' else -1,r) for q,b,w,d,r in result['table']}
        cases=[]
        for k in range(9):
            lo=-k if k<8 else -7
            initial={2}|({-k} if k<8 else set())
            bits={x:int(x in initial) for x in range(lo,3)}
            state=head=steps=0
            def done():
                if shared:return state==n+2 or (k<8 and state==n and head==lo-1)
                return state>=n
            while not done() and steps<limit:
                assert lo<=head<=2
                bit=bits[head]
                w,d,state=table[state,bit]
                bits[head]=w
                head+=d;steps+=1
            want=n if k<8 else n+2 if shared else n+1
            assert done() and state==want
            assert head==(-k-1 if k<8 else -8)
            assert {x for x,b in bits.items() if b}==initial
            cases.append(dict(case=k,steps=steps,exit_state=state,exit_head=head,status='PASS'))
        records.append(dict(file=name,status='PASS',cases=cases))
    return records

def main():
    if not __debug__:
        raise SystemExit('Run with assertions enabled; -O and -OO are unsupported.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=dict(baseline=baseline(),detector_positive_controls=detector_controls())
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
