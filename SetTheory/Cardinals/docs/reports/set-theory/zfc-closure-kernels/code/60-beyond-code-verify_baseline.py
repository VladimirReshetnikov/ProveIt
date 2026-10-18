#!/usr/bin/env python3
"""Independent literal bootstrap, renumbering, and source-control audit.

Uses only the Python standard library. Does not invoke a proof assistant or
infer nonhalting from a finite run. The imported tables/program are attributed
in THIRD_PARTY_NOTICES.txt and pinned in provenance.json.
"""
import argparse
from collections import deque
import hashlib,json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OLD_SHA='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
CANONICAL_SHA='8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797'
PROGRAM_SHA='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def parse_table(path):
    start=None;rows={}
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R')
        rows[q,b]=(w,d,t)
    assert start is not None
    return start,rows

def literal_zipper(table,start,steps,halt):
    # The two finite lists grow only as visited. End = nearest cell, unlike
    # the set-of-one-positions interpreter in the baseline research driver.
    left=[];right=[0];q=start;head=0;minimum=0;maximum=0;visits=set()
    for tick in range(steps):
        assert q!=halt,('premature halt',tick)
        symbol=right.pop()if right else 0
        visits.add((q,symbol));write,d,q=table[q,symbol]
        if d=='R':left.append(write);head+=1
        else:
            right.append(write)
            right.append(left.pop()if left else 0)
            head-=1
        minimum=min(minimum,head);maximum=max(maximum,head)
    cells={head-1-i for i,bit in enumerate(reversed(left))if bit}
    cells.update(head+i for i,bit in enumerate(reversed(right))if bit)
    return q,head,sorted(cells),len(visits),minimum,maximum

def increment(bits):
    out=list(bits)
    for i in range(len(out)-1,-1,-1):
        if out[i]==0:out[i]=1;break
        out[i]=0
    return out

def strip(bits,value,count):
    out=list(bits)
    while out and count:
        count-=out.pop()==value
    return out

def control_audit(data):
    raw=(data/'Prog254.v').read_text()
    part=raw.split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    token=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+token+r'),\s*('+token+r')\)',part)
    assert len(nodes)==6459
    graph=json.loads((data/'program_cases.json').read_text())
    assert graph['source_sha256']==PROGRAM_SHA
    leaves=[];pending=[(0,[])];seen=set()
    while pending:
        node,path=pending.pop();assert node not in seen;seen.add(node)
        for b in (1,0):
            op,*args=nodes[node][b].split();r=int(args[0])if args else None
            if op=='CN':pending.append((r,path+[b]))
            else:leaves.append((''.join(map(str,path+[b])),op,r))
    leaves.sort()
    assert [list(v)for v in leaves]==graph['sites']
    assert len(seen)==6459
    trie={}
    for i,(path,op,r)in enumerate(leaves):
        node=trie
        for bit in map(int,path):
            assert 'leaf'not in node
            node=node.setdefault(bit,{})
        assert not node;node['leaf']=i
    def decode(pc):
        node=trie;k=0
        while 'leaf'not in node:
            assert 0 in node and 1 in node
            node=node[pc[k]if k<len(pc)else 0];k+=1
        assert 1 not in pc[k:]
        return node['leaf']
    cases=[];targets=[]
    for i,(path,op,r)in enumerate(leaves):
        bits=list(map(int,path))
        for zero in ((True,False)if op=='CD'else(None,)):
            cases.append([i,path,op,r,zero])
            if op=='CH':target=None
            else:
                if op=='CI'or op=='CD'and not zero:pc=increment(bits)
                elif op=='CD':pc=increment(strip(bits,0,1))
                elif op=='CB':pc=increment(strip(bits,0,r))
                else:assert op=='CC';pc=strip(bits,1,r)
                target=decode(pc)
            targets.append(target)
    assert cases==graph['cases']and targets==graph['targets']and decode([])==graph['first']==0
    # Also check the compact graph consumed by the C++ abstract interpreter.
    lines=(data/'program_graph.txt').read_text().splitlines()
    assert tuple(map(int,lines[0].split()))==(6460,0)
    by_site=[[]for _ in leaves]
    for case,target in zip(cases,targets):by_site[case[0]].append(-1 if target is None else target)
    for i,((path,op,r),line)in enumerate(zip(leaves,lines[1:])):
        fields=line.split();ts=by_site[i]
        expected=[op[1],str(-1 if r is None else r),str(ts[0]),str(ts[1]if len(ts)>1 else -1)]
        assert fields==expected
    assert len(lines)==6461
    return dict(source_nodes=6459,leaves=6460,checked_guard_successors=len(cases),initial_site=0,
                source_parse='independent iterative traversal',path_semantics='explicit Boolean-list carry and strip')

def verify():
    data=ROOT/'data';old=data/'zfc_permutation252_old.tm';can=data/'zfc_permutation252.tm'
    assert sha(old)==OLD_SHA and sha(can)==CANONICAL_SHA
    assert sha(data/'Prog254.v')==PROGRAM_SHA
    start,t=parse_table(can);old_start,u=parse_table(old)
    meta=json.loads((data/'renumbering.json').read_text())
    rho={int(q):r for q,r in meta['old_to_canonical'].items()}
    assert start==0 and old_start==64 and len(t)==len(u)==504
    assert {q for q,b in t}==set(range(252))
    assert set(t)=={(q,b)for q in range(252)for b in(0,1)}
    assert all(n in range(253)for _,_,n in t.values())
    assert sum(n==252 for _,_,n in t.values())==1
    assert {(rho[q],b):(w,d,rho[n])for(q,b),(w,d,n)in u.items()}==t
    seen=set();pending=deque([start])
    while pending:
        q=pending.popleft()
        if q in seen or q==252:continue
        seen.add(q);pending.extend(t[q,b][2]for b in(0,1))
    assert len(seen)==252
    q,h,ones,visited,minimum,maximum=literal_zipper(t,start,82552,252)
    boot=meta['blank_prefix']
    assert(q,h,ones)==(94,2,boot['all_one_positions'])
    assert ones[0]==1 and ones[1]==42 and len(ones)==77
    cells=set(ones);cursor=43;blocks=[]
    while any(x>=cursor for x in cells):
        assert cursor not in cells and cursor+1 in cells
        cursor+=1;length=0
        while cursor in cells:cursor+=1;length+=1
        blocks.append(length-1)
    assert blocks==[0]*9+boot['spares']and len(blocks)==74
    result=dict(status='PASS',working_states=252,transitions=504,halting_transitions=1,
                graph_reachable_states=252,canonical_sha256=CANONICAL_SHA,old_sha256=OLD_SHA,
                exact_renumbering=True,blank_steps=82552,final_state=94,final_head=2,
                complete_one_positions=ones,one_count=77,primary_blocks=blocks[:9],spare_blocks=blocks[9:],
                visited_transition_pairs=visited,head_minimum=minimum,head_maximum=maximum,
                source_control=control_audit(data),
                scope='independent finite checks only; no fresh Lean/Coq endpoint build; no new nonhalting theorem')
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path)
    args=ap.parse_args();result=verify();text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
