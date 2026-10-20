#!/usr/bin/env python3
"""Common exact machine, source-census, canonicalization and blank-start checks."""
from pathlib import Path
import argparse, csv, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[1]
K_SHA = 'd1ad27580fb8ec41c183760e738a03b1651cc7e2bebc2d48a29a893ca8b34e40'
SOURCE_SHA = 'b8f0b7ef8b9f41329509335f844c5fce94ea9b6cfa8f8a3ca7ebb9fe8c736c13'
MAP_SHA = '8d77f4dcddc9966ba58b0cb8515d604334983e86b51580b546960b1e1d1a7151'

def need(condition, message):
    if not condition: raise ValueError(message)

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump(path, value): Path(path).write_text(json.dumps(value, indent=2) + '\n')

def parse(path):
    rows = {}; start = None
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):
            need(start is None, 'Duplicate start declaration'); start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,z = line.split(); q,b,w,z = map(int,(q,b,w,z))
            need((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R'), 'Invalid row')
            rows[q,b] = (w, 1 if d=='R' else -1, z)
    states = {q for q,b in rows}
    need(start in states and set(rows)=={(q,b) for q in states for b in (0,1)}, 'Incomplete table')
    missing = {z for w,d,z in rows.values()}-states
    need(len(missing)==1, 'Expected one distinguished halt target')
    return rows,start,missing.pop(),states

def encode(table, start=0):
    return ('#! start %d\n'%start + ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'
        for (q,b),(w,d,z) in sorted(table.items()))).encode()

def canonical(table, start, halt):
    order = [start]; seen = {start}
    for q in order:
        for b in (0,1):
            z = table[q,b][2]
            if z!=halt and z not in seen: seen.add(z); order.append(z)
    need(seen=={q for q,b in table}, 'Unreachable declared state')
    labels = {q:i for i,q in enumerate(order)}; labels[halt] = len(order)
    return {(labels[q],b):(w,d,labels[z]) for (q,b),(w,d,z) in table.items()},labels

def source_metrics(path):
    need(sha(path)==SOURCE_SHA, 'Source hash differs')
    sites = json.loads(Path(path).read_text()); leaves={}; prefixes=set()
    for pc,op,arg in sites:
        need(isinstance(pc,str) and pc and set(pc)<={'0','1'} and pc not in leaves, 'Invalid source address')
        need(op in ('CI','CD','CB','CC','CH'), 'Unknown primitive')
        if op in ('CI','CD'): need(type(arg) is int and 0<=arg<9, 'Invalid register')
        elif op in ('CB','CC'): need(type(arg) is int and arg>=1, 'Invalid jump depth')
        else: need(arg is None, 'Invalid halt argument')
        leaves[pc]=(op,arg); prefixes.update(pc[:i] for i in range(len(pc)))
    need(not set(leaves)&prefixes and len(prefixes)==len(leaves)-1, 'Incomplete prefix tree')
    need(all(p+b in leaves or p+b in prefixes for p in prefixes for b in ('0','1')), 'Missing source branch')
    nodes=set()
    def tree(p):
        n=leaves[p] if p in leaves else (tree(p+'0'),tree(p+'1'))
        nodes.add(n); return n
    tree('')
    metrics=dict(instructions=len(sites),dag_nodes=len(nodes),maximum_depth=max(map(len,leaves)),
        maximum_zero_run=max(len(s) for p in leaves for s in p.split('1')),
        guarded_cases=sum(2 if op=='CD' else 1 for pc,op,arg in sites))
    need(metrics==dict(instructions=4581,dag_nodes=209,maximum_depth=38,maximum_zero_run=6,guarded_cases=5956), 'Source census differs')
    return sites,metrics

def bootstrap(table):
    q=0;head=0;ones=set()
    for tick in range(409835):
        need(q!=254, 'Premature halt during initialization')
        b=int(head in ones);w,d,q=table[q,b]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    need(q==84 and head==-5, 'Blank bootstrap endpoint differs')
    need(min(ones)==head-1, 'Nonblank tape to the left of the marker')
    # At this checked dispatcher the address is empty. The first right-hand 1
    # marks the end of the zero gap; B(v)=0 1^(v+1) encodes each register.
    header=min(x for x in ones if x>=head); pos=header+1; values=[]
    while pos<=max(ones):
        need(pos not in ones and pos+1 in ones, 'Malformed unary register block')
        pos+=1;start=pos
        while pos in ones:pos+=1
        values.append(pos-start-1)
    need(pos==max(ones)+1 and len(values)==176, 'Wrong register/spare count')
    physical=[0]*9
    logical=[3,0,0,0,3,0,0,0,0]
    permutation=[6,2,0,4,3,7,8,5,1]
    for i,j in enumerate(permutation):physical[j]=logical[i]
    need(values[:9]==physical and values[9:]==[1]*167, 'Wrong initialized registers')
    need(header-head==181 and len(ones)==351, 'Wrong initialized gap or support')
    return dict(status='EXACT_BLANK_BOOTSTRAP_PASS',steps=409835,k_state=q,head=head,
        logical_registers=logical,physical_register_map=permutation,zero_gap=181,extra_gap=117,
        spare_count=167,spare_values=1,one_cells=sorted(ones),one_cell_count=len(ones),
        all_unlisted_cells=0,scope='Exact complete tape after the first 409835 blank-start transitions.')

