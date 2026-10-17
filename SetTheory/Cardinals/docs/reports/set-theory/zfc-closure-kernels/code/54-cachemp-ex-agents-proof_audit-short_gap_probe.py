#!/usr/bin/env python3
"""Finite ordinary audit of source path budget and literal short-gap transitions.

No general simulation, nonhalting, or consistency claim. Pinned ProveIt source
is read as data. Existing table and decoder attribution remains unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
TABLE_SHA = '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
PROGRAM_SHA = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
PHYSICAL = (6,2,0,4,3,7,8,5,1)


def read_table(raw):
    table = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,m,t = line.split()
        key = int(q),int(b)
        assert key not in table
        table[key] = int(w),m,int(t)
    return table


def read_nodes(path):
    body = path.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
    assert len(nodes) == 6459
    return nodes


def decode(nodes,pc):
    node,path = 0,''
    for _ in range(len(nodes)+1):
        bit = pc[len(path)] if len(path)<len(pc) else '0'
        path += bit
        op,*arg = nodes[node][int(bit)].split()
        if op == 'CN': node = int(arg[0]);continue
        return dict(consumed=path,operation=op,argument=int(arg[0]) if arg else None,
                    clean='1' not in pc[len(path):])
    raise AssertionError('decoder did not terminate')


def strip(path,bit,n):
    while n and path:
        n -= path[-1] == bit
        path = path[:-1]
    return path


def increment(path):
    prefix = path.rstrip('1')
    return prefix[:-1]+'1' if prefix else None


def successor(path,op,arg,zero):
    if op == 'CI' or (op == 'CD' and not zero): return increment(path)
    if op == 'CD': return increment(strip(path,'0',1))
    if op == 'CB': return increment(strip(path,'0',arg))
    if op == 'CC': return strip(path,'1',arg)
    raise AssertionError('source halt reached unexpectedly')


def paint(pc,distance,values,spares,head):
    assert len(pc)<=distance
    ones = {head-1,head+distance} | {head+i for i,b in enumerate(pc) if b=='1'}
    pos = head+distance+1
    for n in values+spares:
        pos += 1
        ones.update(range(pos,pos+n+1))
        pos += n+1
    return ones


def run_prefix(table,n):
    q,h,ones = 64,0,set()
    for _ in range(n):
        assert q != 254
        w,m,q = table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h += 1 if m=='R' else -1
    return q,h,ones


def integer_tape_prefix(table,n):
    """Independent bounded literal replay using a bit-vector, from blank."""
    q,h,bits,offset = 64,0,0,512
    for _ in range(n):
        assert q != 254 and h+offset >= 0
        mask = 1 << (h+offset)
        write,move,target = table[(q,1 if bits & mask else 0)]
        bits = (bits | mask) if write else (bits & ~mask)
        h = h+1 if move=='R' else h-1
        q = target
    support = set()
    while bits:
        low = bits & -bits
        support.add(low.bit_length()-1-offset)
        bits -= low
    return q,h,support


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--fuel', type=int, default=100000)
    parser.add_argument('--table', type=Path, default=ROOT/'sources/candidate-permutation252/zfc_permutation252_old.tm')
    parser.add_argument('--program', type=Path, default=ROOT/'agents/machine_reduction/Prog254.v')
    args = parser.parse_args()
    tb,pb = args.table,args.program
    assert hashlib.sha256(tb.read_bytes()).hexdigest() == TABLE_SHA
    assert hashlib.sha256(pb.read_bytes()).hexdigest() == PROGRAM_SHA
    table = read_table(tb.read_bytes())
    mutant = {k: (w,m,252 if t == 204 else t) for k,(w,m,t) in table.items() if k[0] != 204}
    assert [k for k,v in table.items() if v[2] == 204 and k[0] != 204] == [(172,1)]
    nodes = read_nodes(pb)
    R0 = [0,0,3,2,0,0,2,0,1]
    physical0 = [R0[PHYSICAL.index(i)] for i in range(9)]
    spare0 = [0,0,0,0,0,0,0,0,0,1]
    seedones = paint('',19,physical0,spare0,3)
    q,h,ones = run_prefix(mutant,15963)
    assert (q,h,ones) == (96,3,seedones)
    assert integer_tape_prefix(mutant,15963) == (q,h,ones)
    logical = []
    R,pc,distance = R0.copy(),'',19
    for t in range(100):
        d = decode(nodes,pc)
        path,op,r = d['consumed'],d['operation'],d['argument']
        row = dict(step=t,pc=pc,consumed=path,operation=op,argument=r,registers=R.copy(),distance=distance)
        logical.append(row)
        if len(path) > distance:
            row['exceeds_distance'] = True
            row['header_bit_alternative'] = decode(nodes,pc+'1')
            break
        zero = R[r] == 0 if op == 'CD' else None
        nxt = successor(path,op,r,zero)
        if op == 'CI': R[r] += 1
        elif op == 'CD' and not zero: R[r] -= 1
        if nxt is None: distance += 1
        pc = nxt or ''
    cases = []
    for label,tbl in [('baseline',table),('R252',mutant)]:
        R,pc,gap,head,spares,q = R0.copy(),'',19,3,spare0.copy(),96
        ones = seedones.copy()
        entries = []
        for i in range(30):
            dec = decode(nodes,pc)
            path,op,r = dec['consumed'],dec['operation'],dec['argument']
            if len(path) > gap:
                entries.append(dict(instruction=i,status='source_depth_exceeds_budget',**dec,gap=gap))
                break
            zero = R[r] == 0 if op == 'CD' else None
            nxt = successor(path,op,r,zero)
            outgap,outhead,outpc = gap+(nxt is None),head-(nxt is None),nxt or ''
            newR,newspares = R.copy(),spares.copy()
            if op == 'CI': newR[r] += 1
            elif op == 'CD' and not zero: newR[r] -= 1;newspares.append(0)
            newphysical = [newR[PHYSICAL.index(j)] for j in range(9)]
            target = paint(outpc,outgap,newphysical,newspares,outhead)
            dispatches=[]
            changed_hits=[]
            for moves in range(1,args.fuel+1):
                if q == 254: break
                key=q,int(head in ones)
                if key == (172,1): changed_hits.append(moves)
                w,m,q = tbl[key]
                if w:ones.add(head)
                else:ones.discard(head)
                head += 1 if m == 'R' else -1
                if q == 96:
                    dispatches.append(dict(move=moves,head=head,ones=sorted(ones)))
                    if head==outhead and ones==target: break
            matched = q==96 and head==outhead and ones==target
            entries.append(dict(instruction=i,source_pc=pc,consumed=path,operation=op,argument=r,zero=zero,
                moves=moves,matched=matched,dispatch_visits=dispatches[:6],dispatch_count=len(dispatches),
                changed_hits=changed_hits,status='matched' if matched else 'halt' if q==254 else 'fuel_cutoff',
                expected=dict(pc=outpc,head=outhead,gap=outgap,registers=newR,spares=newspares,ones=sorted(target)),
                actual=dict(state=q,head=head,ones=sorted(ones))))
            if not matched: break
            R,pc,gap,spares = newR,outpc,outgap,newspares
        cases.append(dict(table=label,entries=entries))
    assert logical[-1]['step']==19 and logical[-1]['exceeds_distance']
    assert [e['matched'] for e in cases[0]['entries']] == [True]*17+[False]
    assert cases[0]['entries']==cases[1]['entries']
    divergent=cases[1]['entries'][-1]['dispatch_visits'][0]
    assert divergent['move']==192 and divergent['head']==3
    prefix_total = 15963+sum(e['moves'] for e in cases[1]['entries'][:-1])+divergent['move']
    assert prefix_total==20811
    assert integer_tape_prefix(mutant,prefix_total)==(96,3,set(divergent['ones']))
    out=dict(scope=__doc__,pinned_commit='43026ff42f0939f09b9e95495248cfadcad38e38',
        baseline_sha256=TABLE_SHA,program_sha256=PROGRAM_SHA,
        independent_integer_replay=dict(matched_complete_prefixes=[15963,20811],tape_offset=512),
        initial=dict(blank_prefix=15963,state=96,head=3,gap=19,physical=physical0,logical=R0,spares=spare0,ones=sorted(seedones)),
        source_budget_trace=logical,literal_cases=cases,fuel_per_instruction=args.fuel)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(source_budget_first_exceeded=logical[-1],
        first_17_matched_moves=sum(e['moves'] for e in cases[0]['entries'][:-1]),
        literal=[dict(table=x['table'],tested=len(x['entries']),last_status=x['entries'][-1]['status'],
            last_instruction=x['entries'][-1]['instruction'],last_moves=x['entries'][-1]['moves'],
            dispatch_visits=x['entries'][-1]['dispatch_count']) for x in cases],
        independent_complete_blank_prefixes=[15963,20811]),indent=2))


if __name__=='__main__': main()
