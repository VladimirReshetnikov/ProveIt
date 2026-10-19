#!/usr/bin/env python3
"""Independent boundary239 source, fold, startup, and erasure support audit."""
from pathlib import Path
import json, hashlib, bisect
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]/'combine/zfc239-research-20261019'
OUT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def source(p):
 ss=json.loads(p.read_text());assert len(ss)==6455
 assert len(set(p for p,o,r in ss))==len(ss)
 assert ss==sorted(ss)
 for p,o,r in ss:
  assert set(p)<={'0','1'} and p and o in ['CI','CD','CB','CC','CH']
  assert (r is None if o=='CH' else type(r) is int and r>=0)
  if o in ['CI','CD']:assert r<9
 prefixes={p[:k] for p,o,r in ss for k in range(len(p))}; leaves={p for p,o,r in ss}
 assert not prefixes&leaves
 assert all(p+b in prefixes|leaves for p in prefixes for b in '01')
 return ss

def cfg(ss):
 width=max(len(p) for p,o,r in ss)
 starts=[int(p+'0'*(width-len(p)),2) for p,o,r in ss]
 assert len(set(starts))==len(ss)
 def locate(pc):
  value=int((pc+'0'*width)[:width],2)
  i=bisect.bisect_right(starts,value)-1
  p=ss[i][0]
  assert (pc+'0'*len(p))[:len(p)]==p
  assert pc.rstrip('0')==p.rstrip('0')
  return i
 def inc(p):
  return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b') if p else ''
 def strip(p,bit,count):
  if count==0:return p
  positions=[i for i,b in enumerate(p) if b==bit]
  return p[:positions[-count]] if len(positions)>=count else ''
 assert locate('')==0
 g=[];count=0
 for p,o,r in ss:
  if o=='CI':v=(o,r,locate(inc(p)))
  elif o=='CD':v=(o,r,locate(inc(p)),locate(inc(strip(p,'0',1))))
  elif o=='CB':v=(o,r,locate(inc(strip(p,'0',r))))
  elif o=='CC':v=(o,r,locate(strip(p,'1',r)))
  else:v=(o,r)
  g.append(v);count+=len(v)-2
 return g,count

def rotations(ss,step):
 paths=step['paths'];assert len(set(paths))==len(paths)
 assert not any(a!=b and b.startswith(a) for a in paths for b in paths)
 conversions={'left':[('0','00'),('10','01'),('11','1')], 'right':[('00','0'),('01','10'),('1','11')]}
 used=Counter();out=[]
 for p,o,r in ss:
  matches=[a for a in paths if p.startswith(a)]
  assert len(matches)<=1
  if matches:
   a=matches[0];tail=p[len(a):]
   for x,y in conversions[step['direction']]:
    if tail.startswith(x):p=a+y+tail[len(x):];used[a]+=1;break
   else:raise AssertionError(('Invalid rotation interior',a,p))
  out.append([p,o,r])
 assert set(used)==set(paths)
 return out

def table(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  a,b,c,d,e=line.split();a,b,c,e=map(int,[a,b,c,e]);assert (a,b) not in t
  assert b in (0,1) and c in (0,1) and d in ['L','R'];t[a,b]=(c,d,e)
 states={q for q,b in t};assert len(t)==2*len(states)
 assert set(t)=={(q,b) for q in states for b in [0,1]}
 assert {r for c,d,r in t.values()}-states=={254}
 return t

base=source(ROOT/'formalism/extra/baseline_sites.json')
new=source(ROOT/'candidate239/sites_logical.json')
cert=json.loads((ROOT/'formalism/extra/rotation_certificate.json').read_text())
g0,edges=cfg(base);ss=base;stages=[]
for i,step in enumerate(cert['steps'],1):
 assert step['number']==i
 ss=rotations(ss,step)
 assert [s[1:] for s in ss]==[s[1:] for s in base]
 assert cfg(ss)[0]==g0
 stages.append({'stage':i,'rotations':len(step['paths']),'edges':edges})
assert ss==new and len(stages)==13 and sum(s['rotations'] for s in stages)==25
# Independent hash-consing using nested tuples from prefix leaves.
lookup={p:(o,r) for p,o,r in new};nodes=set()
def dag(p=''):
 t=lookup[p] if p in lookup else (dag(p+'0'),dag(p+'1'))
 nodes.add(t);return t
dag();assert len(nodes)==224

old=table(ROOT/'boundary240/boundary240_old.tm');final=table(ROOT/'candidate239/zfc_boundary239_old.tm')
assert len(old)==480 and len(final)==478
changes={(179,1):(1,'L',215),(187,1):(1,'R',179),(220,1):(1,'R',179),(223,0):(0,'R',23),(223,1):(1,'R',70),(237,0):(0,'R',223)}
expected={k:v for k,v in old.items() if k[0]!=218};expected.update(changes);assert expected==final
incoming=lambda t,q:sorted((s,b,*v[:2]) for (s,b),v in t.items() if v[2]==q)
assert incoming(old,179)==[(161,0,0,'R'),(236,0,0,'R'),(239,0,0,'R')]
assert incoming(old,218)==[(187,1,1,'R'),(220,1,1,'R'),(237,0,0,'R')]
assert incoming(old,223)==[(218,0,0,'L')]
def block(t,q,ell,b,steps):
 cells={-1:ell,0:b};initial=dict(cells);h=0;trace=[]
 for _ in range(steps):
  assert h in cells
  r=cells[h];w,d,n=t[q,r];trace.append([q,r,h,w,d,n]);cells[h]=w;h+=1 if d=='R' else -1;q=n
 assert cells==initial
 return q,h,trace
obligations=[(179,0,0,179,1,1,105),(179,0,1,179,1,5,105),(218,0,0,223,3,1,23),(218,0,1,223,1,1,70),(218,1,0,179,3,1,105),(218,1,1,179,1,3,70)]
blocks=[];fold_support=set()
for oq,ell,b,nq,os,ns,target in obligations:
 a=block(old,oq,ell,b,os);z=block(final,nq,ell,b,ns);assert a[:2]==z[:2]==(target,1)
 fold_support.update((x[0],x[1]) for x in a[2]+z[2]);blocks.append({'case':[oq,ell,b,nq],'old':a,'new':z})
# Independently execute blank initialization as a finite-support dictionary.
q=95;h=0;ones=set();visits=Counter()
for i in range(409691):
 b=int(h in ones);visits[q,b]+=1;w,d,n=final[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=1 if d=='R' else -1;q=n
record=json.loads((ROOT/'candidate239/blank_prefix.json').read_text())
assert (q,h)==(96,-5) and sorted(ones)==record['all_one_positions'] and len(ones)==351
assert record['logical_registers']==[3,0,0,0,3,0,0,0,0]
# Reconstruct the whole initialized register frame from prescribed values.
header=176;physical=[0,0,0,3,0,0,3,0,0];spares=[1]*167
reconstructed={-6,header};pos=header+1
for value in physical+spares:
 pos+=1;reconstructed.update(range(pos,pos+value+1));pos+=value+1
assert ones==reconstructed
baseline=table(ROOT/'baseline/rotation240/zfc_rotation240_old.tm')
erasure_states={80,91,169,106,92,107,125,93,57,167,151,173,56,24,36,54,71,82,94,50,20,2,25}
assert all(final[q,b]==baseline[q,b] for q in erasure_states for b in [0,1])
structural_rows={q:incoming(final,q) for q in [67,80,91,169]}
assert all(incoming(final,q)==incoming(baseline,q) for q in structural_rows)
assert not fold_support&{(147,0),(80,0),(91,1),(169,0),(169,1)}
report={'status':'PASS','source':{'leaf_occurrences':len(new),'edges_per_stage':edges,'halts':sum(x[0]=='CH' for x in g0),'stages':len(stages),'rotations':sum(s['rotations'] for s in stages),'dag_nodes':len(nodes),'max_depth':max(len(p) for p,o,r in new),'operations':dict(Counter(o for p,o,r in new)),'exact_ordered_operands_and_control_successors':True,'all_residuals_equal_as_zero_extended_words':True,'candidate_sites_sha256':sha(ROOT/'candidate239/sites_logical.json')},'fold':{'changes':[{ 'state':k[0],'read':k[1],'new':v } for k,v in changes.items()],'blocks':blocks,'support_rows':sorted(fold_support),'hidden_incoming_ports':False},'startup':{'steps':409691,'state':q,'head':h,'ones':len(ones),'whole_frame_reconstructed':True},'erasure_compatibility':{'all_46_local_support_rows_identical':True,'incoming_sets':structural_rows,'boundary_fold_support_disjoint_from_erasure_patch':True,'remaining_obligation':'q169 scanning1 implies right neighbor1 on new source; direct universal runtime proof is an independent sufficient route'}}
(OUT/'independent_boundary_audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='fold'},indent=2))
