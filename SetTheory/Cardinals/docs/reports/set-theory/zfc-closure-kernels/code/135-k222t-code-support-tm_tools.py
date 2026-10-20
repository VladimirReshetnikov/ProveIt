"""Exact TM row handling and finite source-prefix decoding.

Adapted from K223 seed package build223.py, whose original notices are retained.
The prefix verifier rejects all reads outside its finite known patch.
"""
from collections import defaultdict
import source_language as s

def read_table(raw):
    rows={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R')
        rows[q,b]=(w,1 if d=='R' else -1,z)
    assert starts==[0]
    states={q for q,b in rows}
    assert set(rows)=={(q,b) for q in states for b in (0,1)}
    assert {z for w,d,z in rows.values()}-states=={254}
    return rows

def table_bytes(rows,start=0):
    return (f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'
        for (q,b),(w,d,z) in sorted(rows.items()))).encode('ascii')

def decoder_map(table,tree):
    groups=defaultdict(set);paths=defaultdict(list)
    def visit(n,p,q):
        if s.leaf(n):return
        groups[q].add(n);paths[q].append(p)
        for bit in (0,1):
            if s.leaf(n[bit]):continue
            tape={i:int(v) for i,v in enumerate(p+str(bit))};tape[-1]=1
            before=tape.copy();h,state=len(p),q
            for tick in range(100):
                if h==len(p)+1:break
                assert h in tape,('unknown decoder read',p,state,h)
                w,d,state=table[state,tape[h]];tape[h]=w;h+=d
            assert tape==before and h==len(p)+1
            visit(n[bit],p+str(bit),state)
    visit(tree,'',84)
    return groups,paths

def sole(groups,q):
    assert len(groups[q])==1
    return next(iter(groups[q]))

def canonical(table):
    order=[0];labels={0:0}
    for q in order:
        for bit in (0,1):
            z=table[q,bit][2]
            if z!=254 and z not in labels:labels[z]=len(order);order.append(z)
    assert set(order)=={q for q,b in table}
    labels[254]=len(order)
    return {(labels[q],b):(w,d,labels[z]) for (q,b),(w,d,z) in table.items()},labels
