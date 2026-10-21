#!/usr/bin/env python3
"""Independent finite source/blank audit of the rho6 sampler rewiring.

No candidate generator or symbolic-runtime code is imported. This checks finite
objects, the complete blank prefix, and the exact local register permutation.
The all-natural macro/calculus argument is in ../research/rho6-proof.md, not inferred from runs.
Run: python3 code/audit.py [--root /path/to/unpacked/package]
"""
from pathlib import Path
import json,hashlib,time,argparse
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);args=ap.parse_args()
ROOT=args.root.resolve();UP=ROOT/'inputs/upstream216';NEW=ROOT/'machine';OUT=ROOT/'evidence'
assert __debug__, 'Run without Python -O; assertions carry the finite checks.'
OUT.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read_table(path):
 t={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in t
  t[q,b]=(w,1 if d=='R'else-1,z)
 qs={q for q,b in t};assert set(t)=={(q,b)for q in qs for b in(0,1)}and{z for _,_,z in t.values()}-qs=={254}
 return t

def interval_graph(rows):
 intervals={}
 for i,(p,op,arg)in enumerate(rows):
  for k in range(len(p)+1):
   v=p[:k]
   if v not in intervals:intervals[v]=[i,i+1]
   else:intervals[v][1]=i+1
 def unwind(p,bit,k):
  for j in range(len(p)-1,-1,-1):
   if p[j]==bit:
    k-=1
    if not k:return intervals[p[:j]][1 if bit=='0'else 0]%len(rows)
  return 0
 out=[]
 for i,(p,op,arg)in enumerate(rows):
  nxt=(i+1)%len(rows)
  ts=[nxt]if op=='CI'else[unwind(p,'0',1),nxt]if op=='CD'else[unwind(p,'0',arg)]if op=='CB'else[unwind(p,'1',arg)]if op=='CC'else[]
  assert op in('CI','CD','CB','CC','CH');out.append(ts)
 return out

def arithmetic_graph(rows):
 bypath={p:i for i,(p,_,_)in enumerate(rows)};depth=max(map(len,bypath));assert len(bypath)==len(rows)
 def leaf(p):
  word=p+'0'*(depth+1)
  for k in range(len(word)+1):
   if word[:k]in bypath:
    assert all(x=='0'for x in p[k:]);return bypath[word[:k]]
  raise AssertionError(p)
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b')if p else''
 def strip(p,bit,k):
  positions=[i for i,b in enumerate(p)if b==bit];return p[:positions[-k]]if len(positions)>=k else''
 out=[]
 for p,op,arg in rows:
  out.append([leaf(inc(p))]if op=='CI'else[leaf(inc(strip(p,'0',1))),leaf(inc(p))]if op=='CD'else[leaf(inc(strip(p,'0',arg)))]if op=='CB'else[leaf(strip(p,'1',arg))]if op=='CC'else[])
 return out

def source_metrics(rows):
 bypath={p:(o,a)for p,o,a in rows};seen=set()
 def visit(p):
  n=bypath[p]if p in bypath else(visit(p+'0'),visit(p+'1'));seen.add(n);return n
 visit('');return {'leaf_occurrences':len(rows),'dag_nodes':len(seen),'maximum_depth':max(len(p)for p,_,_ in rows),'maximum_zero_run':max(len(z)for p,_,_ in rows for z in p.split('1'))}

beg=time.monotonic()
pins={UP/'k216.native.tm':'2efb7adf9cfcbea58197a2bde2610b22f58b647f05385bc716b036242be6fa6c',UP/'sites216.compact.json':'7f9d4f321b7a7d56013056b1ad6be2723538c43ea2d73548bcd0e35f0381bde0',NEW/'k216-rho6.native.tm':'37ec2b16d410f5cde9ee9b28f14033066a33d31bf736f3adc6134979d2658010',NEW/'sites216.json':'e83df4fb78e288f5fd717b20a0d82419f511dfcb79fa4dfc1b351f3fef6b3730'}
assert all(sha(p)==h for p,h in pins.items()), 'A pinned finite input changed.'
old=read_table(UP/'k216.native.tm');new=read_table(NEW/'k216-rho6.native.tm');oldsrc=json.loads((UP/'sites216.compact.json').read_text());newsrc=json.loads((NEW/'sites216.json').read_text());assert len(oldsrc)==len(newsrc)==4751
changes=[{'index':i,'before':a,'after':b}for i,(a,b)in enumerate(zip(oldsrc,newsrc))if a!=b]
assert [c['index']for c in changes]==[973,978,1151,1156]
lo,hi=902,1185;perm={3:5,5:3}
for i,(a,b)in enumerate(zip(oldsrc,newsrc)):
 want=a.copy()
 if lo<=i<hi and want[1]in('CI','CD'):want[2]=perm.get(want[2],want[2])
 assert b==want
G=interval_graph(oldsrc);assert G==arithmetic_graph(oldsrc)==interval_graph(newsrc)==arithmetic_graph(newsrc)
inbound=[(i,t)for i,ts in enumerate(G)if not lo<=i<hi for t in ts if lo<=t<hi]
outbound=[(i,t)for i in range(lo,hi)for t in G[i]if not lo<=t<hi]
assert inbound==[(896,902)]and outbound==[(1179,1185)]
assert all(oldsrc[i][1]!='CH'for i in range(lo,hi))
rowchanges=[{'row':list(k),'before':list(old[k]),'after':list(new[k])}for k in sorted(old)if old[k]!=new[k]]
assert rowchanges==[{'row':[199,1],'before':[1,1,166],'after':[1,1,12]},{'row':[206,0],'before':[0,1,186],'after':[0,1,76]}]
assert len(new)==432 and len({q for q,b in new})==216
M={int(k):v for k,v in json.loads((UP/'canonicalization.json').read_text())['native_to_canonical'].items()};qs={q for q,b in new};assert set(M)==qs|{254}and set(M.values())==set(range(217))and M[0]==0 and M[254]==216 and M[84]==84
canonical={(M[q],b):(w,d,M[z])for(q,b),(w,d,z)in new.items()};canonpath=NEW/'k216-rho6.tm'
canonical_bytes=('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(canonical.items()))).encode()
if canonpath.exists():assert canonpath.read_bytes()==canonical_bytes, 'Delivered canonical table differs from the literal state bijection.'
else:canonpath.write_bytes(canonical_bytes)
steps=313133;q=h=0;ones=set();trace=hashlib.sha256();touched=set();minhead=maxhead=0
for tick in range(steps):
 b=int(h in ones);w,d,z=new[q,b];touched.add((q,b));trace.update(f'{q},{h},{b},{w},{d},{z}\n'.encode())
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d;q=z;minhead=min(minhead,h);maxhead=max(maxhead,h)
assert(q,h)==(84,-5)
assert not({tuple(c['row'])for c in rowchanges}&touched)
# A second interpreter uses a dense finite array with checked zero exterior,
# reads the canonical file independently, and normalizes labels for trace audit.
ct={}
for line in canonpath.read_text().splitlines():
 if line.startswith('#')or not line:continue
 a,b,c,d,e=line.split();ct[int(a),int(b)]=(int(c),d,int(e))
assert len(ct)==432 and set(ct)==set(canonical)
for key,(w,d,z)in canonical.items():assert ct[key]==(w,'R'if d==1 else'L',z)
reached={0};todo=[0]
while todo:
 u=todo.pop()
 for bit in(0,1):
  z=new[u,bit][2]
  if z!=254 and z not in reached:reached.add(z);todo.append(z)
assert reached==qs
canon_receipt={'status':'EXACT_ALL_ROW_STATE_BIJECTION_PASS','native_sha256':sha(NEW/'k216-rho6.native.tm'),'canonical_sha256':sha(canonpath),'native_to_canonical':M,'working_states':216,'rows':432,'initial_native':0,'initial_canonical':0,'dispatcher_native':84,'dispatcher_canonical':84,'halt_native':254,'halt_canonical':216,'all_rows_checked':432,'all_working_states_directed_graph_reachable':True,'scope':'The checked bijection commutes with every transition and preserves symbols, movement, initial state, and halt. Induction gives identical behavior on every binary tape. Directed-graph reachability is not a blank-run visitation claim.'}
(NEW/'canonicalization.json').write_text(json.dumps(canon_receipt,indent=2)+'\n')
invM={v:k for k,v in M.items()};radius=max(-minhead,maxhead)+100;offset=radius;tape=bytearray(2*radius+1);state=0;head=offset;trace2=hashlib.sha256();visited=[]
for tick in range(steps):
 assert 0<head<len(tape)-1;symbol=tape[head];write,move,nxt=ct[state,symbol];shift=1 if move=='R'else-1
 trace2.update(f'{invM[state]},{head-offset},{symbol},{write},{shift},{invM[nxt]}\n'.encode());tape[head]=write;head+=shift;state=nxt
assert state==M[q]and head-offset==h and trace.digest()==trace2.digest()
dense_ones={i-offset for i,b in enumerate(tape)if b};assert ones==dense_ones
# Complete expected frame, independently constructed from the literal unary
# convention B(n)=0 1^(n+1), after fixed physical-register permutation.
logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
for j,k in enumerate((6,2,0,4,3,7,8,5,1)):physical[k]=logical[j]
expected={h-1,h+64+80};pos=h+64+80+1
for v in physical+[1]*130:
 expected.update(range(pos+1,pos+v+2));pos+=v+2
assert ones==expected and len(ones)==277
result={'status':'INDEPENDENT_FINITE_SOURCE_AND_COMPLETE_BLANK_PASS','scope':'Finite source/register-permutation/control-flow/table/canonicalization and complete blank-prefix checks. No finite simulation substitutes for the all-natural primitive runtime or inherited calculus proof.','source_changes':changes,'source_permutation':{'interval':[lo,hi],'register_swap':[3,5],'input_entry':902,'normal_exit':1185,'inbound':inbound,'outbound':outbound},'metrics':source_metrics(newsrc),'guarded_edges':sum(map(len,G)),'row_changes':rowchanges,'working_states':216,'rows':432,'startup':{'steps':steps,'native_state':q,'canonical_state':state,'head':h,'gap':80,'logical_registers':logical,'unit_spares':130,'one_cells':len(ones),'ones':sorted(ones),'minimum_visited_head':minhead,'maximum_visited_head':maxhead,'complete_zero_exterior':True,'sparse_dense_trace_sha256':trace.hexdigest(),'changed_rows_absent':True},'sha256':{'new_table':sha(NEW/'k216-rho6.native.tm'),'new_source':sha(NEW/'sites216.json'),'canonical_table':sha(canonpath),'upstream_table':sha(UP/'k216.native.tm'),'upstream_source':sha(UP/'sites216.compact.json'),'driver':sha(Path(__file__))},'seconds':time.monotonic()-beg}
(OUT/'source_blank.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('startup','source_changes')},indent=2));print('STARTUP', {k:v for k,v in result['startup'].items()if k!='ones'})
