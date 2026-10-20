#!/usr/bin/env python3
"""Independent exact-source bucket certificate check with literal blank replay.
No invariant generator is imported. Explicit checks work under Python -O.
"""
from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
import trie_cfg as base
ROOT=Path(__file__).resolve().parent;H=Path(sys.argv[1]).resolve()if len(sys.argv)>1 else ROOT/'results'
need=base.need;sha=base.digest
D=json.loads((H/'invariants.json').read_text());B=json.loads((H/'proof.json').read_text())
source=H/'sites.json';table=H/'candidate.tm';boot=B['startup'];seed=boot['logical_seed']
need(sha(source)==B['source_sha256'] and sha(table)==B['table_sha256'],'input hash')
need(D['threshold']==8 and D['seed']==seed,'domain and seed')
need(D['source_files']==['inputs/sites.json']*2,'source location')
need(D['source_sha256']==[sha(source)]*2,'source hash')
ordered,G,initial=base.cfg(json.loads(source.read_text()))
need(D['ordered']==D['ordered06']==ordered and D['graph']==G and D['initial_site']==initial,'independent CFG')
S=D['states'];need(len(S)==len(G),'mask count')
for i,ss in enumerate(S):need(ss is None or type(ss)is list and len(ss)==9 and all(type(m)is int and 0<m<512 for m in ss),('mask domain',i))
need(S[initial]is not None and all(S[initial][r]>>v&1 for r,v in enumerate(seed)),'initial inclusion')
checks=0
for i,(ins,ss)in enumerate(zip(G,S)):
    if ss is None or ins[0]=='HALT':continue
    if ins[0]=='JUMP':
        target=S[ins[1]];need(target is not None and all(a&~b==0 for a,b in zip(ss,target)),('jump closure',i));checks+=1;continue
    r=ins[1]
    for value in range(10):
        if not(ss[r]>>min(8,value)&1):continue
        if ins[0]=='INC':j,nxt=ins[2],value+1
        elif value==0:j,nxt=ins[3],0
        else:j,nxt=ins[2],value-1
        target=S[j];need(target is not None and target[r]>>min(8,nxt)&1 and all(k==r or ss[k]&~target[k]==0 for k in range(9)),('bucket closure',i,value));checks+=1
T={};start=None
for line in table.read_text().splitlines():
    if line.startswith('#! start '):start=int(line[9:])
    if not line or line.startswith('#'):continue
    q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'table row');T[q,b]=(w,1 if d=='R'else -1,z)
Q={q for q,b in T};need(set(T)=={(q,b)for q in Q for b in(0,1)}and {z for w,d,z in T.values()}-Q=={254},'complete table')
need(start==0,'start label');q=0;h=0;ones=set()
for _ in range(boot['steps']):
    w,d,q=T[q,int(h in ones)]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
need((q,h,sorted(ones))==(84,boot['head'],boot['complete_one_cells']),'independent exact literal startup')
p=boot['header']+1;values=[]
while p<=max(ones):
    need(p not in ones and p+1 in ones,'word delimiter');p+=1;n=0
    while p in ones:n+=1;p+=1
    values.append(n-1)
need(len(values)>=10 and [values[j]for j in B['physical_map']]==seed,'parsed logical seed')
expected={h-1,boot['header']};p=boot['header']+1
for value in values:p+=1;expected.update(range(p,p+value+1));p+=value+1
need(ones==expected and boot['header']-h>=64,'whole frame')
R=dict(status='PASS_INDEPENDENT_SOURCE_BUCKET_AND_EXACT_STARTUP',checks=checks,source_sites=len(G),initial_site=initial,logical_seed=seed,table_sha256=sha(table),source_sha256=sha(source),certificate_sha256=sha(H/'invariants.json'),checker_sha256=sha(Path(__file__)),cfg_checker_sha256=sha(Path(base.__file__)),startup_steps=boot['steps'],reachable_sites=sum(x is not None for x in S),assertions_required=False,scope='Universal source induction from the exact blank startup seed. Runtime source implementation remains a separately replayed theorem; this is not a binary-window certificate.')
(H/'independent_invariants.json').write_text(json.dumps(R,indent=2)+'\n');print(json.dumps(R,indent=2))
