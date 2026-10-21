#!/usr/bin/env python3
"""Independent source/blank audit of zero-spare CB1 DROP-first215.
Uses no supplied source resolver or TM simulator. Does not rederive the separate
universal unary/list-induction certificate or the inherited logical calculus.
"""
from pathlib import Path
import json,hashlib,gzip,argparse
ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline',type=Path,default=ROOT/'ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/commands120',help='Directory containing accepted commands120 k215.native.tm and sites215.json')
parser.add_argument('--candidate',type=Path,default=ROOT/'root_work/zero_cb120',help='Directory containing machine.native.tm, source.sites.json and optional runtime receipts')
parser.add_argument('--out',type=Path,default=Path(__file__).with_name('zero_cb120_audit.json'),help='JSON audit output')
args=parser.parse_args()
BASE=args.baseline
P=args.candidate
OUT=args.out
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(path):
 T={};start=None
 for line in path.read_text().splitlines():
  if line.startswith('#! start '):assert start is None;start=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert b in(0,1)and w in(0,1)and d in('L','R');assert(q,b)not in T
  T[q,b]=w,1 if d=='R'else-1,z
 return start,T

def source_graph(rows):
 n=len(rows);leaves={p:i for i,(p,op,a)in enumerate(rows)};assert len(leaves)==n
 intervals={};prefixes=set()
 for i,(p,op,a)in enumerate(rows):
  for j in range(len(p)+1):
   if p[:j]not in intervals:intervals[p[:j]]=[i,i+1]
   else:intervals[p[:j]][1]=i+1
   if j<len(p):prefixes.add(p[:j])
 assert not prefixes&set(leaves)
 assert all(p+b in prefixes or p+b in leaves for p in prefixes for b in('0','1'))
 assert len(prefixes)==n-1
 graph=[]
 for i,(p,op,a)in enumerate(rows):
  assert op in('CI','CD','CB','CC','CH')
  if op=='CH':graph.append([]);continue
  if op=='CI':graph.append([(i+1)%n]);continue
  ch='0'if op in('CD','CB')else'1';k=1 if op=='CD'else a
  for j in range(len(p)-1,-1,-1):
   if p[j]==ch:
    k-=1
    if k==0:
     target=intervals[p[:j]][int(ch=='0')]%n;break
  else:target=0
  graph.append([target,(i+1)%n]if op=='CD'else[target])
 # Independent binary-counter resolver, including the no-stray-one check.
 D=max(len(p)for p in leaves)
 def first(p):
  word=p+'0'*(D+1)
  for j in range(1,D+1):
   if word[:j]in leaves:
    assert '1'not in p[j:];return leaves[word[:j]]
  raise AssertionError('No successor')
 def inc(p):return format((int(p,2)+1)%2**len(p),'0'+str(len(p))+'b')if p else''
 def cut(p,b,k):
  pos=[i for i,x in enumerate(p)if x==b];return p[:pos[-k]]if len(pos)>=k else''
 for i,(p,op,a)in enumerate(rows):
  if op=='CI':e=[first(inc(p))]
  elif op=='CD':e=[first(inc(cut(p,'0',1))),first(inc(p))]
  elif op=='CB':e=[first(inc(cut(p,'0',a)))]
  elif op=='CC':e=[first(cut(p,'1',a))]
  else:e=[]
  assert e==graph[i]
 return graph

assert sha(BASE/'k215.native.tm')=='da83e8de52f4d9536cee2d5ed4af4311308bda51196d18891b96e4bc9ca6cb4f'
assert sha(BASE/'sites215.json')=='d5c994e3d0c8fe26dd337aca48e5f25ff4f28fd18973f2c04c99589d6ba3f53d'
start,T=table(P/'machine/zc215.native.tm');oldstart,oldT=table(BASE/'k215.native.tm')
assert start==74 and oldstart==0
states={q for q,b in T};assert len(states)==215 and len(T)==430
assert set(T)=={(q,b)for q in states for b in(0,1)}
assert {z for w,d,z in T.values()}-states=={254}
changes={k:v for k,v in T.items()if oldT[k]!=v}
assert changes=={(8,1):(1,1,103),(198,0):(0,-1,40)}
reached={74};todo=[74]
for q in todo:
 for b in(0,1):
  z=T[q,b][2]
  if z!=254 and z not in reached:reached.add(z);todo.append(z)
assert reached==states
old=json.loads((BASE/'sites215.json').read_text());new=json.loads((P/'source/zc215.sites.json').read_text())
expected=[r.copy()for r in old]
expected[7][0]='011100';expected[8][0]='011101';expected.insert(9,['01111','CB',1]);assert new==expected
og=source_graph(old);ng=source_graph(new)
mapidx=lambda i:i+(i>=9)
for i,es in enumerate(og):
 want=[mapidx(x)for x in es]
 if i==7:want[0]=9
 assert ng[mapidx(i)]==want,(i,ng[mapidx(i)],want)
assert ng[9]==[0]
# Every new return change is therefore contained in the fetch/restoration block.
# Replay the complete blank prefix using a finite dictionary containing both
# written zero and one cells; unvisited positions evaluate to zero.
tape={};q=74;h=0;trace=hashlib.sha256();used=set()
for tick in range(117004):
 b=tape.get(h,0);used.add((q,b));w,d,z=T[q,b]
 trace.update(f'{q} {h} {b} {w} {d} {z}\n'.encode())
 tape[h]=w;h+=d;q=z
assert(q,h)==(84,-4)
ones=sorted(i for i,b in tape.items()if b)
assert ones[0]==-5 and ones[1]==80
p=81;values=[]
while p<=ones[-1]:
 assert tape.get(p,0)==0 and tape.get(p+1,0)==1
 p+=1;c=0
 while tape.get(p,0):p+=1;c+=1
 values.append(c-1)
assert p==ones[-1]+1 and len(values)==76
physical=values[:9];spares=values[9:];PHY=(6,2,0,4,3,7,8,5,1)
logical=[physical[i]for i in PHY]
assert logical==[1,0,5,0,0,0,0,0,0]
assert len(spares)==67 and set(spares)=={0,1}
# Construct the entire expected frame independently from numeric registers.
expected_ones={-5,80};p=81
for v in values:
 p+=1;expected_ones.update(range(p,p+v+1));p+=v+1
assert expected_ones==set(ones)
# Decode finite initial stack: P(0,P(0,1))=5.
def pair(a,b):return(a+b)*(a+b+1)//2+b
assert pair(0,pair(0,1))==5
# Exercise all small scheduler states as an independent finite corroboration.
# The universal equations follow directly from the source loops described below.
def run_source_until_read(N,L,X=0):
 regs=[N,0,5,0,0,0,X,0,L];pc=0
 for k in range(100000):
  if pc==10:return regs,k
  op,a=new[pc][1:];e=ng[pc]
  if op=='CI':regs[a]+=1;pc=e[0]
  elif op=='CD':positive=regs[a]>0;regs[a]-=int(positive);pc=e[int(positive)]
  else:assert op in('CB','CC');pc=e[0]
 raise AssertionError('Scheduler did not terminate')
for N in range(1,40):
 for L in range(40):
  r,k=run_source_until_read(N,L)
  assert r[0]==(N if L else N+1)
  assert r[8]==(L-1 if L else N-1)
  assert r[6]==0 and r[7]==0
record={'status':'INDEPENDENT_SOURCE_AND_WHOLE_BLANK_AUDIT_PASS','source_sha256':sha(P/'source/zc215.sites.json'),'table_sha256':sha(P/'machine/zc215.native.tm'),'states':len(states),'transition_rows':len(T),'graph_reachable_working_states':len(reached),'start_state':74,'halt_state':254,'changed_rows':[[*k,*v]for k,v in sorted(changes.items())],'source':{'old_leaves':len(old),'new_leaves':len(new),'new_ordinal':9,'new_instruction':['CB',1],'new_guarded_cases':sum(2 if r[1]=='CD' else 1 for r in new),'independent_resolvers':2,'exact_full_source_recipe':True,'only_changed_old_cfg_edge':[7,'zero',10,9],'new_cfg_edge':[9,0],'all_other_ordinal_edges_transported':True},'blank':{'steps':117004,'state':q,'head':h,'header':80,'gap':20,'logical':logical,'physical':physical,'spares':spares,'one_cells':ones,'visited_interval':[min(tape),max(tape)],'literal_trace_sha256':trace.hexdigest(),'full_zero_exterior_checked':True},'scheduler':{'finite_cases_checked':39*40,'positive_L':'N unchanged; L becomes L-1 before Read','zero_L_positive_N':'N becomes N+1; L becomes N-1 before Read','scratch':'X=Y=0 at Read','universal_reason':'The first loop transfers old N into L and X; the second restores N to old N+1 and clears X. The inserted CB1 returns to ordinal0, where positive L is decremented before Read. For initial N>=1 no zero-fetch recursion occurs.'},'scope':'Exact recipe/source-CFG transport and finite whole blank run, with direct loop proof of scheduler equations. Does not independently kernel-check the separate all-natural binary certificate or inherited consistency calibration.'}
if(P/'evidence/runtime.json').exists():
 runtime=json.loads((P/'evidence/runtime.json').read_text());cases=json.loads(gzip.decompress((P/'evidence/runtime_cases.json.gz').read_bytes()))
 assert runtime['table_sha256']==record['table_sha256']and runtime['source_sha256']==record['source_sha256']
 expectedcases=[(i,b)for i,r in enumerate(new)for b in((False,True)if r[1]=='CD'else(False,))]
 assert [(r['site_index'],r['positive'])for r in cases]==expectedcases
 assert len(cases)==6177 and runtime['cases']==6177
 assert all(len(c['duration'])==13 and c['duration'][0]>0 and all(v>=0 for v in c['duration'])for c in cases)
 assert runtime['rules']==sum(c['symbolic_steps']for c in cases)
 assert set(map(tuple,runtime['native_rows']))==set(T)
 record['runtime_saved_record_audit']={'status':'PASS','cases':len(cases),'rules':runtime['rules'],'covered_rows':runtime['row_count'],'positive_affine_durations':True,'scope':'Pins, order, affine positivity, aggregate counts and declared complete row coverage; proof-rule replay is the separate fresh checker run.'}
OUT.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items()if k not in('blank','scheduler')},indent=2))
print('BLANK',record['blank']['steps'],record['blank']['logical'],'ONES',len(ones),'SPARES',len(spares))
