#!/usr/bin/env python3
"""Independent weighted objectives; no final circuit emission or old verifier."""
import argparse,hashlib,json
from collections import Counter
from functools import lru_cache
from pathlib import Path
PINS={
 'complete86_first_root_partitions.py':'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988',
 'complete86_first_root_partitions.md':'7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0',
 'complete86_first_root_partitions.json':'7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5',
 'complete75_asymmetric_scale_tradeoffs.json':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98',
 'complete75_asymmetric_scale_tradeoffs.md':'3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2',
 'complete75_asymmetric_linear_gap_tradeoffs.json':'dcd2c462e8405bc4535682a624832e8a8ad044a86504fd0b46df6700ab5c0f26',
 'complete75_asymmetric_linear_gap_tradeoffs.md':'93aac323a64bf6c7e8946faeddf90de5606d8c133d3bd611a0806269e8f92638',
}
REFERENCE=[[86,178],[87,134],[88,122],[89,112],[90,108],[91,102],[92,80],[93,72],[94,62],[95,54],[96,50],[97,48],[98,44]]
NAMES=['first','main','input','aux','index','transport','strong','linear']
PORTS=['norm_'+n for n in NAMES]
def need(v,m):
 if not v:raise AssertionError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':'))

def partition_masks(mask):
 """Distinct method from the author's restricted-growth traversal."""
 if not mask:yield ();return
 first=mask&-mask;rest=mask^first;sub=rest
 while True:
  group=first|sub
  for tail in partition_masks(mask^group):yield (group,)+tail
  if not sub:break
  sub=(sub-1)&rest
def indices(mask):return [i for i in range(mask.bit_length())if mask>>i&1]

def core_counts(rows,ports):
 definitions={n:(op,a,b)for n,op,a,b in rows};live=set();todo=list(ports)
 while todo:
  x=todo.pop()
  if type(x)is not str or x not in definitions or x in live:continue
  live.add(x);todo.extend(definitions[x][1:])
 core=[row for row in rows if row[0]in live];c=Counter(row[1]for row in core)
 need(definitions['kinner']==('+','Kconstant','wn2')and definitions['local_rhs']==('*','zplus','repunit'),'actual transport core')
 for n,row in {'wn2':('*','w','q'),'q':('+','repunit',1),'tau_square':('*','tau_gap','tau_gap'),'first_root_base':('*','UM','ksn2'),'twice_tau_gap':('+','tau_gap','tau_gap'),'first_signed_gap':('-','twice_tau_gap','R10b'),'first_cross':('*','first_root_base','first_signed_gap'),'norm_first':('+','tau_square','first_cross')}.items():need(n in live and definitions[n]==row,'actual six-gate gap norm '+n)
 need([n for n,op,a,b in core if 'tau_gap'in(a,b)]==['tau_square','twice_tau_gap'],'private gap coordinate')
 return c['*'],c['+']+c['-'],sha(stable(core).encode())

def bases(data):
 asym=data['complete75_asymmetric_scale_tradeoffs.json']['source'];direct={f['name']:f['source']for f in data['complete75_asymmetric_linear_gap_tradeoffs.json']['direct_transfers']};out=[]
 for kind in ['asymmetric_normalized','asymmetric_ordinary','asymmetric_comparison']+[prefix+'_'+suffix for prefix in('linear','auxgap')for suffix in('coupled_units','uncoupled_units','coupled_comparison','uncoupled_comparison','six_comparisons')]:
  if kind.startswith('asymmetric'):
   normalized=kind=='asymmetric_normalized';rows=asym[0 if normalized else 1]['source'];weights=[12,18,32,56 if normalized else 24,7,2,34 if normalized else 22,7];omit=kind=='asymmetric_comparison';six=False
  else:
   prefix,family=kind.split('_',1);uncoupled=family.startswith('uncoupled')or family=='six_comparisons';gap=prefix=='auxgap'
   name=('gap_91_degree128'if uncoupled else'gap_90_degree131')if gap else('linear_90_degree132'if uncoupled else'linear89')
   rows=direct[name];weights=[12,18,20,20 if gap else 24,7,2,22,6 if uncoupled else 7];omit=family.endswith('comparison')or family=='six_comparisons';six=family=='six_comparisons'
  ports=PORTS[:];names=NAMES[:];comparisons=[];res=[]
  if omit:ports.pop(6);names.pop(6);weights.pop(6);comparisons+=['ic22','R16'];res.append(22)
  if six:ports.pop();names.pop();weights.pop();comparisons+=['H17','aux_u_rhs'];res.append(6)
  M,A,core_hash=core_counts(rows,ports+comparisons)
  for coordinate in('gap_root','first_root'):
   w=weights[:];ac=A
   if coordinate=='first_root':w[0]=22;ac-=1
   out.append({'coordinate':coordinate,'kind':kind,'factor_names':names[:],'weights':w,'residual_degrees':res[:],'core_M':M,'core_A':ac,'old_gap_core_sha256':core_hash})
 return out

def counts_by_stirling(n):
 s=[1]+[0]*n
 for i in range(1,n+1):
  nxt=[0]*(n+1)
  for k in range(1,i+1):nxt[k]=s[k-1]+k*s[k]
  s=nxt
 return {k:s[k]for k in range(1,n+1)}

def one_base(b):
 weights=b['weights'];n=len(weights);m=len(b['residual_degrees']);r=max(b['residual_degrees']+[0]);full=(1<<n)-1
 sums=[sum(weights[i]for i in indices(mask))for mask in range(full+1)];hist=Counter();best={};ties=Counter();count=0;choices=0
 def score(partition,anchor):
  ds=[sums[s]for s in partition];g=len(ds);special=anchor is not None and g==1 and m==0
  # Count actual instruction classes, independently of the one-line total.
  group_mult=n-g;residual_count=m+g-int(anchor is not None)
  M=b['core_M']+group_mult+residual_count
  A=b['core_A']+residual_count+max(0,residual_count-1)
  if anchor is not None:M+=int(residual_count>0);A+=1+int(residual_count>0)
  cost=M+A
  need(cost==b['core_M']+b['core_A']+n+3*m+2*g-1-int(special),'independent fully paid count identity')
  degree=2*max(ds+[r])if anchor is None else ds[anchor]+2*max([v for i,v in enumerate(ds)if i!=anchor]+[r])
  return cost,degree,M,A
 for p in partition_masks(full):
  count+=1;hist[len(p)]+=1
  for anchor in [None]+list(range(len(p))):
   choices+=1;cost,degree,M,A=score(p,anchor)
   record={'operations':cost,'predicted_degree':degree,'M':M,'A':A,'partition':[indices(s)for s in p],'anchor':anchor}
   if cost not in best or degree<best[cost]['predicted_degree']:best[cost]=record;ties[cost]=1
   elif degree==best[cost]['predicted_degree']:ties[cost]+=1
 need(dict(hist)==counts_by_stirling(n),'exhaustive Stirling distribution')
 need(choices==sum((g+1)*v for g,v in hist.items()),'all SOS and distinguished anchors')
 # Separate minimax subset DP, then independent choice of anchored subset.
 inf=10**9
 @lru_cache(None)
 def minimax(mask,k):
  if not mask:return 0 if k==0 else inf
  if k<=0 or k>mask.bit_count():return inf
  low=mask&-mask;best_value=inf;sub=mask
  while sub:
   if sub&low:best_value=min(best_value,max(sums[sub],minimax(mask^sub,k-1)))
   sub=(sub-1)&mask
  return best_value
 dp={}
 for g in range(1,n+1):
  dummy=tuple([1<<i for i in range(g-1)]+[full^((1<<(g-1))-1)])
  cost=score(dummy,None)[0];d=2*max(r,minimax(full,g));dp[cost]=min(dp.get(cost,inf),d)
  anchored=inf;sub=full
  while sub:
   rest=minimax(full^sub,g-1)
   if rest<inf:anchored=min(anchored,sums[sub]+2*max(r,rest))
   sub=(sub-1)&full
  cost=score(dummy,0)[0];dp[cost]=min(dp.get(cost,inf),anchored)
 need(dp=={k:v['predicted_degree']for k,v in best.items()},'separate subset-DP objective cross-check')
 return {**b,'partitions':count,'objective_choices':choices,'partitions_by_group_count':dict(hist),'best_by_cost':[dict(best[k],tie_count=ties[k])for k in sorted(best)],'subset_dp_states':minimax.cache_info().currsize}

def verify(root):
 data={}
 for name,pin in PINS.items():
  raw=(root/name).read_bytes();need(sha(raw)==pin,'pin '+name)
  if name.endswith('.json'):data[name]=json.loads(raw)
 bs=bases(data);need(len(bs)==26,'thirteen bases twice');results=[one_base(b)for b in bs]
 # Previously saved first-root base ledgers independently authenticate the
 # core counts on every kind actually represented by a full saved packet.
 explicit={f['base']['kind']:f['base']for f in data['complete86_first_root_partitions.json']['frontier_sources']}
 for b in bs:
  if b['coordinate']=='first_root'and b['kind']in explicit:
   old=explicit[b['kind']];need((b['core_M'],b['core_A'])==(old['core_ledger']['M'],old['core_ledger']['A']),'saved actual core ledger')
   ws=b['weights'][:];ws[5]=3;need(ws==old['weights']and b['residual_degrees']==old['residual_degrees'],'saved base vector')
 candidates=[dict(w,coordinate=b['coordinate'],kind=b['kind'])for b in results for w in b['best_by_cost']]
 points=sorted({(w['operations'],w['predicted_degree'])for w in candidates});front=[p for p in points if not any(q!=p and q[0]<=p[0]and q[1]<=p[1]for q in points)]
 improvements=[p for p in front if not any(q[0]<=p[0]and q[1]<=p[1]for q in REFERENCE)]
 witnesses=[w for w in candidates if (w['operations'],w['predicted_degree'])in front]
 count={'bases':26,'partitions':sum(b['partitions']for b in results),'objective_choices':sum(b['objective_choices']for b in results),'subset_DP_cross_checks':26,'best_by_cost_records':len(candidates),'predicted_winner_operations':sum(w['operations']for w in candidates),'predicted_winner_M':sum(w['M']for w in candidates),'predicted_winner_A':sum(w['A']for w in candidates)}
 need(count['partitions']==59262 and count['objective_choices']==298672,'independent whole family cardinalities')
 return {'status':'PASS_EXHAUSTIVE_WEIGHTED_OBJECTIVES_ONLY','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'counts':count,'bases':results,'predicted_frontier':[list(p)for p in front],'improvements_over_reviewed39':[list(p)for p in improvements],'frontier_metadata_witnesses':witnesses,'reviewed39_reference':REFERENCE,'scope':'Weighted26-base objectives only: actual saved JSON ancestry used to recount gap cores, proved first-root delta applied arithmetically; no author Python/old verify, no complete child circuit emission, no new verified universal bound.'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root);text=json.dumps(r,sort_keys=True,indent=2)+'\n'
 if a.expect:need(a.expect.read_text()==text,'fresh exact objective receipt')
 if a.output:a.output.write_text(text)
 print(r['status'],r['counts']);print('FRONTIER',r['predicted_frontier']);print('NEW',r['improvements_over_reviewed39'])
