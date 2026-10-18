#!/usr/bin/env python3
"""Independent sparse/dense blank replay and finite full-tape instruction checks.

Uses only the Python standard library. Finite regressions are supplementary to
the ordinary invariant proof and universal expanded runtime replay.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse, json, time, gzip

TABLE_SHA = '6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0'
CANONICAL_SHA = '64ddeb2c01c3e9c7feffaffaad87266a270716c9307892a0445bf869b988984d'
SOURCE_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)

def read(path):
    table = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '): start = int(line.split()[-1])
        if not line or line.startswith('#'): continue
        q,b,w,d,r = line.split()
        q,b,w,r = map(int,(q,b,w,r))
        assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in table
        table[q,b] = (w, 1 if d == 'R' else -1, r)
    assert len(table) == 484
    return table, start

def increment(pc):
    a = list(pc)
    for i in range(len(a)-1, -1, -1):
        if a[i] == '0': a[i] = '1'; return ''.join(a), False
        a[i] = '0'
    return ''.join(a), True

def strip(pc, bit, count):
    while count and pc:
        count -= int(pc[-1] == bit)
        pc = pc[:-1]
    return pc

def frame(head, pc, span, logical, spares):
    assert span >= len(pc)
    ones = {head-1, head+span}
    ones.update(head+i for i,b in enumerate(pc) if b == '1')
    values = [None] * 9
    for i,j in enumerate(PHYSICAL): values[j] = logical[i]
    p = head+span+1
    for v in values+spares:
        assert isinstance(v,int) and v >= 0
        ones.update(range(p+1,p+v+2)); p += v+2
    return ones

def blank_sparse(table, start, dispatcher, expected):
    q,h,ones = start,0,set()
    used = Counter()
    for n in range(1000001):
        if q == dispatcher and h == -5 and ones == expected:
            return n,q,h,ones,used
        key = q,int(h in ones)
        assert key in table, ('halt before prescribed frame', n,q,h)
        w,d,q = table[key]; used[key] += 1
        if w: ones.add(h)
        else: ones.discard(h)
        h += d
    raise AssertionError('No prescribed root frame within the explicit bound')

def blank_dense(table, start, steps):
    size = max(q for q,b in table)+1
    rows = [None]*(2*size)
    for (q,b),r in table.items(): rows[2*q+b] = r
    origin = steps+1
    tape = bytearray(2*steps+3)
    h,q = origin,start
    for _ in range(steps):
        w,d,q = rows[2*q+tape[h]]
        tape[h] = w; h += d
    return q,h-origin,{i-origin for i,b in enumerate(tape) if b}

def main():
    assert __debug__, 'Assertions must be enabled.'
    ap = argparse.ArgumentParser()
    ap.add_argument('--candidate',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a = ap.parse_args()
    a.output.mkdir(parents=True,exist_ok=True)
    raw, canonical = a.candidate/'machine_old.tm',a.candidate/'machine.tm'
    source = a.candidate/'sites_logical.json'
    assert sha256(raw.read_bytes()).hexdigest() == TABLE_SHA
    assert sha256(canonical.read_bytes()).hexdigest() == CANONICAL_SHA
    assert sha256(source.read_bytes()).hexdigest() == SOURCE_SHA
    table,start = read(raw); ct,cs = read(canonical)
    assert start == 95 and cs == 0
    sites = json.loads(source.read_text()); assert len(sites) == 6459
    expected = frame(-5,'',181,[3,0,0,0,3,0,0,0,0],[1]*167)
    assert len(expected) == 351
    n,q,h,ones,bootused = blank_sparse(table,start,96,expected)
    cn,cq,ch,cones,cused = blank_sparse(ct,cs,86,expected)
    assert n == cn and (q,h,ones) == (96,-5,expected) and (cq,ch,cones) == (86,-5,expected)
    assert blank_dense(table,start,n) == (q,h,ones)
    assert blank_dense(ct,cs,n) == (cq,ch,cones)
    blank = dict(status='PASS_RETURN242_EXACT_BLANK_FRAME',steps=n,working_states=242,
                 sparse_dense_agreement_both_numberings=True,canonical_state=cq,
                 old_state=q,head=h,marker=-6,header=176,span=181,
                 logical_registers=[3,0,0,0,3,0,0,0,0],spare_values=[1]*167,
                 one_count=len(ones),all_one_positions=sorted(ones),all_other_cells_zero=True,
                 table_sha256=TABLE_SHA,canonical_sha256=CANONICAL_SHA,
                 old_row_counts=[[*k,v] for k,v in sorted(bootused.items())])
    (a.output/'blank.json').write_text(json.dumps(blank,indent=2)+'\n')
    print('Blank prefix:',n,'transitions, four exact executions agree.',flush=True)
    used,records,total = Counter(),[],0
    began = time.monotonic()
    for index,(pc,op,r) in enumerate(sites):
        for zero in ((True,False) if op == 'CD' else (None,)):
            serial = len(records)
            logical = [(17*serial+11*j+3*index+7)%23 for j in range(9)]
            if op == 'CD': logical[r] = 0 if zero else 1+(13*serial+7*r)%23
            spares = [(serial+2*j+3)%13 for j in range(1+serial%5)]
            span = 64+17*(serial%3)
            tape = frame(0,pc,span,logical,spares)
            output,tail,extra,overflow = logical.copy(),spares.copy(),0,False
            if op == 'CI': output[r]+=1;tail.append(1);successor,overflow=increment(pc)
            elif op == 'CD' and not zero: output[r]-=1;extra=1;successor,overflow=increment(pc)
            elif op == 'CD': successor,overflow=increment(strip(pc,'0',1))
            elif op == 'CB': successor,overflow=increment(strip(pc,'0',r))
            elif op == 'CC': successor=strip(pc,'1',r)
            else: assert op == 'CH';successor=''
            endhead = -int(overflow)
            target = None if op == 'CH' else frame(endhead,successor,span+extra+int(overflow),output,tail)
            state,head = 96,0
            for steps in range(1,20001):
                key = state,int(head in tape)
                assert key in table,('unexpected halt',serial,index,pc,op,r,zero)
                w,d,state = table[key];used[key]+=1
                if w:tape.add(head)
                else:tape.discard(head)
                head+=d
                if op == 'CH' and state == 254:break
                if op != 'CH' and state == 96 and head == endhead and tape == target:break
            else:raise AssertionError(('finite fixture exceeded bound',serial,index,pc))
            total+=steps
            records.append(dict(index=index,pc=pc,op=op,r=r,zero=zero,logical_registers=logical,
                                spare_values=spares,initial_span=span,steps=steps,final_head=head,final_state=state))
    assert len(records) == 8390 and set(used) == set(table)
    result = dict(status='PASS_RETURN242_FINITE_LITERAL_CASES',cases=len(records),source_leaves=len(sites),
                  steps=total,covered_rows=len(used),total_rows=484,whole_tape_endpoints_checked=True,
                  minimum_steps=min(c['steps']for c in records),maximum_steps=max(c['steps']for c in records),
                  primary_fixtures='Independent deterministic values 0..22; positive tested register 1..23.',
                  span_values=[64,81,98],spare_lengths=[1,2,3,4,5],seconds=time.monotonic()-began,
                  table_sha256=TABLE_SHA,source_sha256=SOURCE_SHA,
                  row_counts=[[*k,v] for k,v in sorted(used.items())],
                  scope='Finite examples only; universal proof is supplied separately.')
    (a.output/'literal.json').write_text(json.dumps(result,indent=2)+'\n')
    with gzip.GzipFile(filename=str(a.output/'literal-cases.json.gz'),mode='wb',mtime=0)as stream:
        stream.write((json.dumps(records,indent=2)+'\n').encode())
    print(json.dumps({k:v for k,v in result.items() if k!='row_counts'},indent=2),flush=True)

if __name__ == '__main__':main()
