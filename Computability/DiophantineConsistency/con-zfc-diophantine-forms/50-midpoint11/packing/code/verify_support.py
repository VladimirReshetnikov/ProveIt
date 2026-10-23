#!/usr/bin/env python3
"""Exact support-isolation audit from the literal parent circuit, no search."""
from pathlib import Path
import collections,hashlib,itertools,json,math,sys
from audit_parent_packing import add,mul,shift_positive
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'nine'))
from port_polynomial import parse

def residuals(path):
 d=json.loads(path.read_text());names=d['variables']+d['constants'];n=len(d['variables']);z=(0,)*len(names)
 env={}
 for i,name in enumerate(names):
  e=list(z);e[i]=1;env[name]={tuple(e):1}
 def get(x):return ({z:x} if x else {}) if isinstance(x,int) else env[x]
 for name,op,a,b in d['source']:
  env[name]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),-1 if op=='-' else 1)
 rs=[shift_positive(add(get(a),get(b),-1),n) for a,b in d['comparisons']]
 return rs,d['variables']

def main():
 data=json.loads((ROOT/'data/coefficient_recipes.json').read_text())
 w=json.loads((ROOT/'data/weights.json').read_text())['weights'];W=max(w)
 assert len(w)==32 and w[0]==0 and len(set(w))==32 and all(x>0 for x in w[1:])
 assert W==190
 source,names=residuals(ROOT/'upstream/parent_system.json')
 source60,names60=residuals(ROOT/'upstream/parent_system60.json')
 assert names==names60==data['variables']
 def shift_one(poly,index):
  out={}
  for e,c in poly.items():
   for k in range(e[index]+1):
    x=list(e);x[index]=k;x=tuple(x);out[x]=out.get(x,0)+c*math.comb(e[index],k)
  return {e:c for e,c in out.items() if c}
 assert [shift_one(r,names.index('z')) for r in source]==source60
 rows=[source[i-1] for i in data['row_order_one_based']]
 normalized=[]
 for row in rows:
  grouped={}
  for mon,c in row.items():
   a,ports=mon[:31],mon[31:];assert sum(a)<=2
   factor=math.factorial(2-sum(a))*math.prod(math.factorial(e) for e in a)
   grouped.setdefault(a,{})[ports]=c*factor
  normalized.append(grouped)
 for actual,row in zip(normalized,data['rows']):
  expected={}
  for t in row:
   leaf=t['leaf'];expected[tuple(t['alpha'])]=({(0,)*4:leaf*t['sign']} if isinstance(leaf,int) else {tuple(x['powers']):x['coefficient']*t['sign'] for x in data['recipes'][leaf]})
  assert actual==expected
 pairs=list(itertools.combinations_with_replacement(range(32),2))
 alphas=[]
 for i,j in pairs:
  a=[0]*31
  if i:a[i-1]+=1
  if j:a[j-1]+=1
  alphas.append(tuple(a))
 support=set().union(*(set(r) for r in normalized));assert len(support)==71
 sums=[w[i]+w[j] for i,j in pairs]
 bysum=collections.defaultdict(list)
 for a,s in zip(alphas,sums):bysum[s].append(a)
 for a in support:
  s=sum(x*y for x,y in zip(a,w[1:]));assert bysum[s]==[a]
 assert len(bysum)<528 # Explicitly certify that full B2 is not being used.
 targets=[2*W+j*(2*W+1) for j in range(22)]
 targetmap={x:j for j,x in enumerate(targets)};occupied={};checks=0;hits=0
 for j,row in enumerate(normalized):
  for a,poly in row.items():
   d=targets[j]-sum(x*y for x,y in zip(a,w[1:]));assert d>=0 and d not in occupied
   occupied[d]=(j,a)
   for beta,s in zip(alphas,sums):
    checks+=1
    k=targetmap.get(d+s)
    if k is not None:
     assert k==j and a==beta;hits+=1
 assert hits==sum(map(len,normalized))==136
 assert max(occupied)==targets[-1] and normalized[-1][(0,)*31]=={(0,)*4:2}
 nine=json.loads((ROOT/'quartic/QUADRATIC_TARGETS.json').read_text())
 assert nine['weights']==w[1:] and nine['target_spacing']==2*W+1 and nine['target_maximum']==22*(2*W+1)
 for j,row in enumerate(nine['rows']):
  assert row['target_exponent']==targets[j]+1
  actual={tuple(t['alpha']):parse(t['weighted_coefficient']) for t in row['terms']}
  expected={}
  for mon,c in source60[data['row_order_one_based'][j]-1].items():
   a,p=mon[:31],mon[31:];fac=math.factorial(2-sum(a))*math.prod(math.factorial(e) for e in a)
   expected.setdefault(a,{})[p]=c*fac
  assert actual==expected
  assert set(actual)==set(normalized[j])
  for t in row['terms']:
   assert t['weight']==sum(a*b for a,b in zip(t['alpha'],w[1:]))
   assert t['encoding_exponent']==row['target_exponent']-t['weight']
 out={'status':'PASS','maximum_weight':W,'weights':w,'all_quadratic_monomials':528,'protected_monomials':71,'distinct_pair_sums':len(bysum),'unprotected_collisions_permitted':528-len(bysum),'source_terms':136,'exact_source_expansion_pairs_checked':checks,'target_hits':hits,'all_target_hits_are_required_diagonal_terms':True,'all_136_encoded_coefficients_occupy_distinct_positions':True,'parent_circuits_match_after_z_old_equals_z_new_plus_one':True,'both_parent_families_have_identical_supports':True,'parent_source_sha256':hashlib.sha256((ROOT/'upstream/parent_system.json').read_bytes()).hexdigest(),'sun_targets':targets,'nine_targets':[x+1 for x in targets],'scope':'Finite exact algebra and combinatorics; does not certify the inherited infinite semantic or number theoretic reductions.'}
 (ROOT/'certificates/support_isolation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
