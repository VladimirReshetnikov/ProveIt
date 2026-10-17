#!/usr/bin/env python3
"""Literal bootstrap search for cache-MP tables with physical role permutations.

Only the explicitly whitelisted register-selector target rows are retargeted.
No arithmetic operation is accelerated. Safe hits require the entire binary
root frame, including complete spare suffix/exterior, and explicit certificates
for both formula fields and all paired stack entries. All hits are replayed
independently with Python from actual blank start0 (not a prepared tape).
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import subprocess
import time

import safe_seed254

SKIP=(60,44,31,56,38,40,28,64,69)
PHYS=(6,2,0,4,3,7,8,5,1)
SELECTORS={(169,1),(173,1),(18,1),(201,1),(21,1),(25,1),(39,1),
           (47,1),(49,1),(53,1),(65,1),(70,1),(72,1),(93,1)}

def read_table(raw):
    table={}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=int(q),int(b)
        assert key not in table
        table[key]=int(w),d,int(t)
    states={q for q,b in table}
    assert len(table)==2*len(states)
    assert all((q,b) in table for q in states for b in (0,1))
    assert all(t==254 or t in states for w,d,t in table.values())
    return table

def encode(table):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items()))).encode()

def mutate(table,p):
    return {k:(w,d,SKIP[p[SKIP.index(t)]] if k in SELECTORS else t) for k,(w,d,t) in table.items()}

def prefix(table,start):
    q,h,ones=start,0,set();trace=[]
    while not ones:
        assert len(trace)<255 and q!=254
        w,d,nxt=table[q,0];trace.append(dict(state=q,head=h,write=w,direction=d,target=nxt))
        if w:ones.add(h)
        h+=1 if d=='R' else -1;q=nxt
    assert q==1 and {x-h for x in ones}=={1}
    return q,h,ones,trace

def literal(table,steps,start=0):
    q,h,ones=start,0,set()
    for _ in range(steps):
        assert q!=254
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    return q,h,ones

def repaint(head,gap,values):
    ones={head-1,head+gap};p=head+gap+1
    for v in values:
        p+=1;ones.update(range(p,p+v+1));p+=v+1
    return ones

def fnv(ones):
    digest=14695981039346656037
    for p in sorted(ones):
        for byte in (p%(1<<64)).to_bytes(8,'little'):
            digest=((digest^byte)*1099511628211)%(1<<64)
    return str(digest)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--samples',type=int,default=4096)
    ap.add_argument('--seed',type=int,default=20261017)
    ap.add_argument('--limit',type=int,default=1000000)
    ap.add_argument('--permutations',type=Path)
    args=ap.parse_args()
    if not __debug__:ap.error('assertions required')
    work=args.output_dir;work.mkdir(parents=True,exist_ok=True)
    raw=args.table.read_bytes();table=read_table(raw)
    for k in SELECTORS:
        assert k in table and k[1]==1 and table[k][2] in SKIP
    assert all(table[k][:2]==(0,'R') for k in SELECTORS)
    _,offset,_,pre=prefix(table,0)
    _,offset64,_,pre64=prefix(table,64)
    rng=random.Random(args.seed)
    if args.permutations:
        maps=[list(map(int,line.split())) for line in args.permutations.read_text().splitlines() if line.strip()]
    else:
        maps=[list(range(9))];seen={tuple(maps[0])}
        while len(maps)<args.samples:
            p=list(range(9));rng.shuffle(p)
            if tuple(p) not in seen:maps.append(p);seen.add(tuple(p))
    assert len({tuple(p) for p in maps})==len(maps)
    assert all(sorted(p)==list(range(9)) for p in maps)
    (work/'rows.txt').write_text(''.join(f'{q} {b} {w} {1 if d=="R" else -1} {t} '
        f'{SKIP.index(t) if (q,b) in SELECTORS else -1}\n' for (q,b),(w,d,t) in sorted(table.items())))
    (work/'permutations.txt').write_text(''.join(' '.join(map(str,p))+'\n' for p in maps))
    cpp=Path(__file__).with_suffix('.cpp');binary=work/'literal-census'
    cmd=['g++','-O3','-std=c++17','-Wall','-Wextra',str(cpp),'-o',str(binary)]
    subprocess.run(cmd,check=True)
    began=time.monotonic()
    with (work/'literal.jsonl').open('w') as out:
        subprocess.run([str(binary),str(work/'rows.txt'),str(work/'permutations.txt'),str(args.limit)],stdout=out,check=True)
    rows=[json.loads(line) for line in (work/'literal.jsonl').read_text().splitlines()]
    assert len(rows)==len(maps)
    elapsed=time.monotonic()-began
    hits=[];replayed_steps=0
    for index,(row,p) in enumerate(zip(rows,maps)):
        assert row['index']==index
        row['post_permutation']=p
        row['logical_to_physical']=[p[x] for x in PHYS]
        if row['outcome']=='safe_root' or index in (0,1,2,3):
            candidate=mutate(table,p)
            assert all(candidate[q,0]==table[q,0] for q,b in candidate)
            q,h,ones=literal(candidate,row['steps']+len(pre));replayed_steps+=row['steps']+len(pre)
            normalized={x-offset for x in ones}
            assert (q,h-offset,len(ones),fnv(normalized))==(row['state'],row['head'],row['one_count'],row['ones_fnv64'])
            row['independent_actual_blank_replay']=True
            if row['outcome']=='safe_root':
                assert sorted(normalized)==row['whole_one_positions']
                values=row['values'];logical=[values[p[x]] for x in PHYS]
                cert=safe_seed254.state(logical);assert cert is not None
                assert q==96 and row['gap']>=40 and ones==repaint(h,row['gap'],values)
                hit=dict(row,actual_blank_steps=row['steps']+len(pre),actual_blank_head=h,
                    actual_blank_one_positions=sorted(ones),safe_certificate=cert,
                    logical_primary=logical,physical_primary=values[:9],spares=values[9:],
                    whole_tape_repaint_equal=True,all_other_cells_blank=True)
                encoded=encode(candidate);hit['table_sha256']=hashlib.sha256(encoded).hexdigest()
                dest=work/f'hit-{index}.tm';dest.write_bytes(encoded);hit['table_path']=str(dest)
                (work/f'hit-{index}.json').write_text(json.dumps(hit,indent=2)+'\n')
                hits.append(hit)
                print(json.dumps(dict(hit=index,steps=hit['actual_blank_steps'],logical=logical,permutation=p)),flush=True)
    result=dict(scope=__doc__,source_table=str(args.table),source_sha256=hashlib.sha256(raw).hexdigest(),
        working_states=len(table)//2,transitions=len(table),halt_label=254,start_label=0,
        selector_whitelist=sorted(SELECTORS),current_logical_to_physical=list(PHYS),
        literal_blank_prefix_start0=pre,blank_head_translation=offset,
        literal_blank_prefix_start64=pre64,blank_head_translation_start64=offset64,
        samples=len(maps),seed=args.seed,normalized_step_limit=args.limit,
        outcomes=dict(Counter(row['outcome'] for row in rows)),elapsed_literal_seconds=elapsed,
        independently_replayed_python_steps=replayed_steps,cases=rows,hits=hits,
        cpp_sha256=hashlib.sha256(cpp.read_bytes()).hexdigest(),compile_command=cmd,
        status='completed finite census')
    (work/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('working_states','samples','outcomes','elapsed_literal_seconds','status')},indent=2),flush=True)

if __name__=='__main__':main()
