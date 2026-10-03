#!/usr/bin/env python3
"""Independent weighted minima: threshold bin packing and analytic anchor bounds.
No import/execution of author optimizer or historical subset minimax DP.
"""
import argparse,copy,hashlib,json,math
from functools import lru_cache
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'neary_woods_tail_quotient_all16.json':'13282605960e782b2389042f2ebd6ce12f3961c8c48e579a86739bc1e77ee6da','neary_woods_tail_quotient_all16.py':'0ed907103449c2fea80113ef39c407531c4350c8e8207a888c23f5a299f664b9','neary_woods_tail_quotient_all16.md':'c0cb462011e78cbb879ca64300f48d3dfb25241de66b0de08dcc5d9d1d7f47e4'}
AUTHOR_PINS={'neary_woods_universal_tail_partitions.py': 'e8c629e104dbd7fcb60881d23c61d68649f0f96e86123f008ad61ee1bee71f83', 'neary_woods_universal_tail_partitions.json': 'a0f113e07ac5ff57d957e2dfbf1cb5c974fe1ca1476aac14c8e6ea37e95f08d0', 'neary_woods_universal_tail_partitions.md': 'f6673dfebc6966b550ecd364c8f97b4cd02c7043a00070f6efc18a2102a7b387'}
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def floor_formula(weights,r):
 w=sorted(weights,reverse=True);prefix=0;candidates=[dict(kind='SOS singletons',degree=2*max(r,w[0]))]
 for k,x in enumerate(w,1):
  prefix+=x;candidates.append(dict(kind='largest-prefix anchor',prefix=k,anchor_weight=prefix,largest_outside=w[k]if k<len(w)else 0,degree=prefix+2*max(r,w[k]if k<len(w)else 0)))
 return min(z['degree']for z in candidates),candidates

def packing(weights,k,cap):
 """Exact decision by descending item placement into sorted load bins.
 Equal-load bins are symmetric. Returns an actual <=k-bin packing or None.
 """
 order=sorted(range(len(weights)),key=lambda i:(-weights[i],i));ordered=tuple(weights[i]for i in order)
 if max(weights)>cap or sum(weights)>k*cap:return None,dict(states=0,reason='largest or total-capacity lower bound')
 suffix=[0]*(len(weights)+1)
 for i in range(len(weights)-1,-1,-1):suffix[i]=suffix[i+1]+ordered[i]
 @lru_cache(None)
 def dfs(i,loads):
  if i==len(ordered):return()
  if suffix[i]>sum(cap-x for x in loads):return None
  w=ordered[i];seen=set()
  for j,load in enumerate(loads):
   if load in seen or load+w>cap:continue
   seen.add(load);nxt=list(loads);nxt[j]+=w;nxt=tuple(sorted(nxt));tail=dfs(i+1,nxt)
   if tail is not None:return((load,load+w),)+tail
  return None
 actions=dfs(0,(0,)*k)
 stats=dict(states=dfs.cache_info().currsize,reason='exact descending-load placement')
 if actions is None:return None,stats
 groups=[[]for _ in range(k)];loads=[0]*k
 for idx,(before,after)in zip(order,actions):
  j=loads.index(before);groups[j].append(idx);loads[j]=after
 need(sorted(i for g in groups for i in g)==list(range(len(weights)))and max(sum(weights[i]for i in g)for g in groups)<=cap,'returned bin-packing witness')
 return[g for g in groups if g],stats

def split_groups(groups,k):
 groups=copy.deepcopy(groups)
 while len(groups)<k:
  j=next(i for i,g in enumerate(groups)if len(g)>1);groups.append([groups[j].pop()])
 need(len(groups)==k and all(groups),'exactly k nonempty groups')
 return groups

def objective(weights,r,groups,anchor):
 sums=[sum(weights[i]for i in g)for g in groups]
 return 2*max([r]+sums)if anchor is None else sums[anchor]+2*max([r]+[s for i,s in enumerate(sums)if i!=anchor])

def solve(base):
 w=base['weights'];r=base['residual'];n=len(w);W=sum(w);floor,candidates=floor_formula(w,r);records=[];proofs=[]
 # One group: exhaustive choice of no anchor or the only group as anchor.
 vals=[(2*max(r,W),None),(W+2*r,0)];one,anchor=min(vals,key=lambda t:t[0]);records.append(dict(groups=1,partition=[list(range(n))],anchor=anchor,degree_upper_bound=one,lower_certificate='exact two one-group finalizers'))
 # Two groups: SOS lower bound2*max(r,largest,ceil(W/2)). For an
 # anchor of weight a and a nonempty complement b, degree=a+2max(r,b)
 # >= W+b >= W+min(w). Our attained SOS bound is no larger.
 cap=max(r,max(w),(W+1)//2);g,stats=packing(w,2,cap);need(g is not None,'balanced two-group lower bound attained')
 two=2*cap;need(two<=W+min(w),'all two-group anchors excluded')
 records.append(dict(groups=2,partition=split_groups(g,2),anchor=None,degree_upper_bound=two,lower_certificate='SOS total/maximum bound; anchor>=total+smallest'))
 proofs.append(dict(groups=2,capacity=cap,packing=stats,anchor_lower_bound=W+min(w)))
 # Three groups: find exact SOS minimax by a threshold decision using a
 # different state space from the author subset-partition optimizer.
 low=max(r,max(w),(W+2)//3);high=W
 checks=[]
 while low<high:
  mid=(low+high)//2;g,stats=packing(w,3,mid);checks.append(dict(capacity=mid,feasible=g is not None,statistics=stats))
  if g is None:low=mid+1
  else:high=mid
 g,stats=packing(w,3,low);need(g is not None,'three-bin winner');below,bstats=packing(w,3,low-1);need(below is None,'three-bin strict lower threshold impossible')
 three=2*low
 # With two nonempty nonanchor groups, their largest >= complement/2,
 # so every anchored three-group objective is at least total W.
 need(three<=W,'all three-group anchors excluded')
 records.append(dict(groups=3,partition=split_groups(g,3),anchor=None,degree_upper_bound=three,lower_certificate='exact three-bin threshold; anchor>=total'))
 proofs.append(dict(groups=3,minimum_capacity=low,thresholds=checks,attaining=stats,one_lower_infeasible=bstats,anchor_lower_bound=W))
 # Every listed weight is positive. The global analytic floor is attained
 # already with four nonempty SOS groups in each of these eight bases.
 need(floor%2==0 and floor>=2*r,'SOS realization of global floor')
 g,stats=packing(w,4,floor//2);need(g is not None,'global floor reached with at most four bins')
 for k in range(4,n+1):records.append(dict(groups=k,partition=split_groups(g,k),anchor=None,degree_upper_bound=floor,lower_certificate='analytic all-partition floor; splitting attaining four-bin packing'))
 proofs.append(dict(groups=4,capacity=floor//2,packing=stats))
 for z in records:
  need(sorted(i for g in z['partition']for i in g)==list(range(n))and len(z['partition'])==z['groups'],'each plan partitions all factors')
  need(objective(w,r,z['partition'],z['anchor'])==z['degree_upper_bound'],'attaining exact weighted objective')
  m=base['ordinary_count'];cost=base['core_operations']+n+3*m-1+2*z['groups']
  if m==0 and z['groups']==1 and z['anchor']==0:cost=base['core_operations']+n
  z.update(operations=cost,base=base['base'],witnesses=base['witnesses'])
 return dict(base=base['base'],weights=w,residual=r,total=W,family_floor=floor,floor_candidates=candidates,proofs=proofs,best_by_group_count=records)

def brute_small(weights,r):
 best={};n=len(weights);groups=[]
 def rec(i):
  if i==n:
   for anchor in[None]+list(range(len(groups))):
    value=objective(weights,r,groups,anchor);k=len(groups);best[k]=min(best.get(k,value),value)
   return
  for g in groups:g.append(i);rec(i+1);g.pop()
  groups.append([i]);rec(i+1);groups.pop()
 rec(0);return best

def frontier(records,witnesses):
 records=sorted((z for z in records if z['witnesses']==witnesses),key=lambda z:(z['operations'],z['degree_upper_bound'],z['base'],z['groups']));out=[];degree=10**9
 for z in records:
  if z['degree_upper_bound']<degree:out.append({k:z[k]for k in('operations','degree_upper_bound','base','groups','witnesses')});degree=z['degree_upper_bound']
 return out

def verify(root):
 root=Path(root)
 for name,digest in PINS.items():need(sha((root/name).read_bytes())==digest,'pinned source ledger '+name)
 data=json.loads((root/'neary_woods_tail_quotient_all16.json').read_text());need(len(data['forms'])==16,'sixteen emitted sources')
 bases=[]
 for i in range(8):
  f=data['forms'][i];other=data['forms'][i+8];inv=f['inventory'];degree=f['degree'];need(inv['native_base']==i and other['inventory']['native_base']==i,'paired eligible native base')
  w=[degree['factor_degree_bounds'][n]for n in inv['factor_ports']];r=max(degree['ordinary_residual_degree_bounds'],default=0)
  need(w==[other['degree']['factor_degree_bounds'][n]for n in other['inventory']['factor_ports']]and exact(f['degree'],other['degree']),'same weighted task at both duration interfaces')
  bases.append(dict(base=i,weights=w,residual=r,witnesses=len(f['auxiliaries']),ordinary_count=len(inv['ordinary_comparisons']),core_operations=f['core_ledger']['operations']))
 searches=[solve(b)for b in bases];records=[z for s in searches for z in s['best_by_group_count']];need(len(records)==120,'all group counts for eight bases')
 # Independent formula check on small actual partitions, including anchors
 # containing several heaviest weights where the largest-only shortcut fails.
 examples=[([100,60,1],0),([10,9,8,1],0),([7],0),([7],10),([4,4,4,4],1),([2,3,5,8,13],7),([1,2,3,4,5,6],0)]
 for w,r in examples:
  bf=brute_small(w,r);floor,_=floor_formula(w,r);need(floor==min(bf.values()),'analytic floor equals independent small Bell enumeration')
  for k in range(1,len(w)+1):
   for cap in range(max(w),sum(w)+1):
    g,_=packing(w,k,cap)
    # Separate tiny labeled-bin exhaustive assignment for feasibility.
    loads=[0]*k
    def assign(i):
     if i==len(w):return True
     for j in range(k):
      if loads[j]+w[i]<=cap:
       loads[j]+=w[i]
       if assign(i+1):loads[j]-=w[i];return True
       loads[j]-=w[i]
     return False
    need((g is not None)==assign(0),'independent tiny assignment feasibility')
 checked=0
 for n,h in AUTHOR_PINS.items():need(sha((root/n).read_bytes())==h,'frozen compared author '+n)
 author=json.loads((root/'neary_woods_universal_tail_partitions.json').read_text());supplied=[z for s in author['searches']for z in s['best_by_group_count']]
 need(len(supplied)==120,'author proposed full task inventory')
 lookup={(z['base'],z['groups']):z for z in supplied};need(len(lookup)==120,'unique author task keys')
 for z in records:
  q=lookup[(z['base'],z['groups'])];need(z['degree_upper_bound']==q['degree_upper_bound']and z['operations']==q['operations']and z['witnesses']==q['witnesses'],'independent optimum versus proposed plan')
  need(sorted(i for g in q['partition']for i in g)==list(range(len(bases[z['base']]['weights'])))and len(q['partition'])==z['groups']and all(q['partition']),'author plan actual partition')
  need(objective(bases[z['base']]['weights'],bases[z['base']]['residual'],q['partition'],q['anchor'])==z['degree_upper_bound'],'proposed plan attains independent minimum');checked+=1
 for b,s in zip(bases,author['searches']):need(b['weights']==s['weights']and b['residual']==s['residual']and b['core_operations']==s['core_operations'],'same frozen author weighted task')
 fronts={str(w):frontier(records,w)for w in(43,44)}
 need([(z['operations'],z['degree_upper_bound'])for z in fronts['43']]==[(253,982),(255,848),(256,802),(257,604),(258,558),(259,404),(260,398),(261,312)],'independent 43-witness frontier')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),compared_author_pins=copy.deepcopy(AUTHOR_PINS),searches=searches,frontiers=fronts,counts={'bases':8,'duration_interfaces_per_base':2,'exact_group_minima':120,'frozen_author_minima_compared':checked,'small_formula_examples':len(examples)},scope='Independent exact minimization of the displayed weighted upper-degree objective on eight authenticated tail bases; not exact polynomial degrees, a source audit, or a bound on other circuit grammars. Different threshold/load-bin algorithm, no optimizer imports.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'floors':[s['family_floor']for s in r['searches']],'frontier43':r['frontiers']['43']}))
if __name__=='__main__':main()
