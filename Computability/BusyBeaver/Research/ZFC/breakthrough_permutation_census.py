#!/usr/bin/env python3
"""Broader bounded literal blank-start search over physical-register bijections.

The native loop executes every binary row literally. The input is the exact
first-write class containing old start64, whose unchanged read0 prefix is
replayed independently. A structural-root hit is independently replayed with
Python; the output records its sufficient Safe-classifier result and all8391
conditional affine checks, even if either fails. Neither a finite negative
nor this filter proves a new machine.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import tempfile
import time

import breakthrough_register_permutation as base


def literal(table, limit):
    q='1'; head=0; ones={1}
    for i in range(limit):
        assert q!='254'
        w,d,q=table[q,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1
    value=14695981039346656037
    for p in sorted(ones):
        for byte in (p%(1<<64)).to_bytes(8,'little'):
            value=((value^byte)*1099511628211)%(1<<64)
    return {'state':int(q),'head':head,'one_count':len(ones),'ones_fnv64':str(value)},ones


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--scratch',type=Path)
    p.add_argument('--samples',type=int,default=4096)
    p.add_argument('--seed',type=int,default=20261016)
    p.add_argument('--limit',type=int,default=1000000)
    a=p.parse_args()
    if not __debug__:p.error('Assertions must remain enabled')
    if not 65<=a.samples<=362880 or not 1<=a.limit<=10000000:p.error('Invalid finite bounds')
    repo=base.REPO;work=a.scratch.resolve() if a.scratch else Path(tempfile.mkdtemp(prefix='zfc-permutation-census-'))
    if work==repo or repo in work.parents or work==Path('/'):p.error('External scratch required')
    work.mkdir(parents=True,exist_ok=True);inputs=base.prepare(repo,work)
    q='64';head=0;ones=set();prefix=[]
    while not ones:
        assert len(prefix)<255
        w,d,nxt=base.T[q,0];prefix.append([q,head,w,d,nxt])
        if w:ones.add(head)
        head+=1 if d=='R' else -1;q=nxt
    assert q=='1' and {x-head for x in ones}=={1}
    maps=[list(range(9))]+[m for _,m in base.family('all36')]+[m for _,m in base.family('remaining28')]
    names=['identity']+[n for n,_ in base.family('all36')]+[n for n,_ in base.family('remaining28')]
    seen={tuple(m) for m in maps};rng=random.Random(a.seed)
    while len(maps)<a.samples:
        m=list(range(9));rng.shuffle(m)
        if tuple(m) not in seen:seen.add(tuple(m));maps.append(m);names.append('random'+str(len(maps)-66))
    raw=work/'rows.txt'
    raw.write_text(''.join(f'{q} {b} {w} {1 if d=="R" else -1} {t} '
      f'{base.SKIP.index(int(t)) if int(q) not in base.CORE and int(t) in base.SKIP else -1}\n'
      for (q,b),(w,d,t) in sorted(base.T.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
    perms=work/'permutations.txt';perms.write_text(''.join(' '.join(map(str,m))+'\n' for m in maps))
    cpp=Path(__file__).with_suffix('.cpp');binary=work/'literal-census'
    compiler=subprocess.check_output(['g++','--version'],text=True).splitlines()[0]
    compile_cmd=['g++','-O3','-std=c++17','-Wall','-Wextra',str(cpp),'-o',str(binary)]
    subprocess.run(compile_cmd,check=True)
    begun=time.monotonic();raw_output=work/'literal.jsonl'
    with raw_output.open('w') as out:subprocess.run([str(binary),str(raw),str(perms),str(a.limit)],stdout=out,check=True)
    rows=[json.loads(l) for l in raw_output.read_text().splitlines()];assert len(rows)==len(maps)
    result={'scope':'Finite literal normalized blank-prefix runs. No binary runtime, general conjugation, spare-space, or consistency-equivalence theorem.',
      'command':[sys.executable,*sys.argv],'python':platform.python_version(),'cpp_sha256':hashlib.sha256(cpp.read_bytes()).hexdigest(),
      'compiler':compiler,'compile_command':compile_cmd,'input_files':inputs,'seed':a.seed,'samples':len(maps),
      'normalized_step_limit':a.limit,'literal_blank_prefix':prefix,'blank_head_translation':head,
      'start_convention':'Every candidate starts at old64 on blank tape; normalized runs omit its exact common first-write prefix.',
      'selection':'65 prior controls, then distinct seeded random bijections. Only first structural root in each run is retained.',
      'structural_root_scope':'Empty PC, gap>=40, exact nine primary blocks and every spare recorded. Safe grammar is sufficient only; spare capacity/value and binary semantics still need proof.',
      'cases':[],'elapsed_literal_seconds':time.monotonic()-begun,'scratch':str(work)}
    for i,(row,m,name) in enumerate(zip(rows,maps,names)):
        assert row['index']==i and row['steps']<=a.limit
        targets={str(base.SKIP[j]):str(base.SKIP[m[j]]) for j in range(9)}
        table={k:(w,d,targets.get(t,t) if int(k[0]) not in base.CORE else t) for k,(w,d,t) in base.T.items()}
        assert all(table[k]==base.T[k] for k in base.BOX_PAIRS)
        assert all(table[q,0]==base.T[q,0] for q,b in table)
        row.update(name=name,physical_permutation=m,table_sha256=hashlib.sha256(base.encoded(table)).hexdigest())
        # Every early halt/root and eight finite controls get an independent interpreter.
        if row['outcome']!='fuel_limit' or i<4 or i in (64,65,len(maps)//2,len(maps)-1):
            actual,tape=literal(table,row['steps'])
            assert all(row[k]==v for k,v in actual.items())
            row['independent_python_final_configuration']=True
            if row['outcome']=='structural_root':
                assert sorted(tape)==row['whole_one_positions']
                frame=base.parse_root(str(row['state']),row['head'],tape,m);assert frame is not None
                row['frame']=frame;row['affine']=base.certify(table,m)
                path=work/(name+'.tm');path.write_bytes(base.encoded(table));row['table_path']=str(path)
        result['cases'].append(row)
    result['outcomes']=dict(Counter(r['outcome'] for r in rows));result['status']='complete'
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('samples','outcomes','elapsed_literal_seconds','status')},indent=2))


if __name__=='__main__':main()
