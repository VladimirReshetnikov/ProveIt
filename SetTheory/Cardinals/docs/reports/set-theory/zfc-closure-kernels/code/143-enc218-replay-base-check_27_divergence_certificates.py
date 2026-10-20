#!/usr/bin/env python3
"""Check only the three received inert divergence certificates; no search/imports."""
import json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent
p=R/'latest219_baseline/candidate-k219/k219.native.tm';T={}
for line in p.read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),-1 if d=='L' else 1,int(z))
C=R/'research218_encoding/COOPERATIVE27_CAP_CERTIFICATES.json'
data=json.loads(C.read_text());certs=[r for r in data['cases'] if r['certificate']]
assert {tuple(r['action']) for r in certs}=={(0,-1,113),(1,-1,113),(1,-1,66)}
# Independently constructed source000/CD8 zero-register, gap0, spare[0] frame.
initial={-1,64}|set(range(66,85,2))
# CD8 at zero skips its sibling and returns at sourcePC01, unchanged registers.
required=initial|{1}
def clean(q,h,S):
 if q!=84 or h-1 not in S or any(x<h-1 for x in S):return False
 headers=[x for x in S if x>=h+52]
 if not headers or min(headers)<h+64:return False
 pos=min(headers)+1;last=max(S);blocks=0
 while pos<=last:
  if pos in S or pos+1 not in S:return False
  pos+=1
  while pos in S:pos+=1
  blocks+=1
 return pos==last+1 and blocks>=10

def step(U,q,h,S):
 b=int(h in S);w,d,z=U[q,b]
 if w:S.add(h)
 else:S.discard(h)
 return z,h+d,[q,h,b,w,d,z]
# Positive completion of the control table is an independent local sanity check.
q=84;h=0;S=set(initial)
for t in range(1,2001):
 q,h,_=step(T,q,h,S)
 if clean(q,h,S):
  assert q==84 and h==0 and S==required
  baseline_steps=t;break
else:raise AssertionError('baseline did not return')
results=[]
for r in certs:
 U={k:v for k,v in T.items() if k[0]!=302}
 U[103,1]=(0,-1,162);U[113,0]=(0,-1,27);U[27,0]=tuple(r['action'])
 q=84;h=0;S=set(initial)
 for t in range(r['prefix_steps']):
  q,h,_=step(U,q,h,S)
  assert not clean(q,h,S),('earlier clean interface endpoint',r['action'],t)
 ep=r['prefix_endpoint']
 assert q==ep['state'] and h==ep['head'] and S==set(ep['ones'])
 assert q==27 and h<0 and all(x>h for x in S)
 c=r['certificate'];start=h;old=set(S);trace=[]
 count=2 if c['kind']=='ONE_WAY_FRESH_BLANK_SWEEP' else 6
 for i in range(count):
  q,h,row=step(U,q,h,S);trace.append(row)
 assert q==27 and h==start-(2 if count==2 else 4)
 assert all(row[1]<=start for row in trace)
 assert all(x>h for x in S) # Entire infinite left half, not only a finite window.
 assert {x for x in S if x>start}=={x for x in old if x>start}
 if count==2:
  assert c['direction']==-1 and c['head']==start
  assert min(old)==c['support_min'] and max(old)==c['support_max']
  assert [[row[0],row[2],row[3],row[4],row[5]] for row in trace]==c['rows']
  assert all(row[2]==0 and row[4]==-1 for row in trace)
  reason='Each step moves strictly left. All future cells were zero and writes stay behind; induction gives an infinite two-state fresh-blank sweep.'
 else:
  assert c['trace']==trace and c['shift']==-4 and c['period']==6
  assert c['initial_head']==start and c['final_head']==h
  assert c['boundary']==start and c['head_max']==start and c['head_min']==h
  assert c['initial_live_ones']==[] and c['final_live_ones']==[]
  assert [(row[0],row[1]-start,row[2],row[3],row[4],row[5]) for row in trace]==[(27,0,0,1,-1,66),(66,-1,0,1,1,198),(198,0,1,1,-1,113),(113,-1,1,0,-1,97),(97,-2,0,1,-1,113),(113,-3,0,0,-1,27)]
  assert S-old=={start,start-2}
  reason='For every h<0 with state27 and all cells x<=h blank, the exact six-step block stays at x<=h, writes only h and h-2, and returns at h-4 with every x<=h-4 blank. Induction translates the block forever; discarded right cells are never read.'
 results.append({'action':r['action'],'status':'INDEPENDENT_DIVERGENCE_CERTIFICATE_ACCEPTED','prefix_steps':r['prefix_steps'],'prefix_endpoint_exactly_replayed':True,'no_earlier_clean_dispatch':True,'prefix_head':start,'period_steps':count,'shift':h-start,'entire_future_half_blank':True,'excluded_right_half_unchanged':True,'proof':reason})
out={'status':'THREE_INDEPENDENT_DIVERGENCE_CERTIFICATES_ACCEPTED','native_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256(C.read_bytes()).hexdigest(),'initial_ones':sorted(initial),'required_ones':sorted(required),'baseline_zero_cd8_steps':baseline_steps,'new_prefix_steps':sum(x['prefix_steps'] for x in results),'additional_period_steps':10,'results':results,'scope':'Three concrete source000/CD8 zero-register primitive-interface divergences only. No extra action enumeration; other reported filter totals not independently rechecked here. No claim about initialized blank-run divergence, global Con(ZFC) calibration, every interpretation, or all smaller machines.'}
(D/'COOPERATIVE27_DIVERGENCE_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
