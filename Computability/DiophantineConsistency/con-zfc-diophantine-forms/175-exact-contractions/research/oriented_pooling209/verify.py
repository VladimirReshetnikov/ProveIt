#!/usr/bin/env python3
"""Independent finite checker. Does not import the compiler or search code."""
from collections import Counter
from pathlib import Path
from math import factorial
import copy, hashlib, json

ROOT=Path(__file__).resolve().parent
def canonical(v):return (json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(v):return hashlib.sha256(canonical(v)).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def read_poly(ts,n,degree):
 p={}
 for c,mon in ts:
  require(type(c)is int and c!=0,'coefficient must be a nonzero integer')
  require(type(mon)is list and len(mon)<=degree,'degree or monomial shape')
  require(all(type(v)is int and 0<=v<n for v in mon),'coordinate range')
  m=tuple(mon);require(tuple(sorted(mon))==m and m not in p,'canonical monomial')
  p[m]=c
 return p
def sum_poly(*pairs):
 ans=Counter()
 for a,p in pairs:
  for mon,c in p.items():ans[mon]+=a*c
 return {mon:c for mon,c in ans.items() if c}
def product(p,q):
 ans=Counter()
 for mon,c in p.items():
  for mm,d in q.items():ans[tuple(sorted(mon+mm))]+=c*d
 return {mon:c for mon,c in ans.items() if c}
def eval_p(p,x):
 ans=0
 for mon,c in p.items():
  for v in mon:c*=x[v]
  ans+=c
 return ans
def check(parent,operations,e,cert):
 n=len(parent['variables']);m=len(e['variables']);names=[v['name'] for v in parent['variables']]
 require(n==218 and m==209,'dimension')
 require(sha(parent)==cert['source_sha256'] and sha(operations)==cert['basis_operation_source_sha256'],'source binding')
 require(sha(e)==cert['output_sha256'],'output binding')
 old=[read_poly(r['terms'],n,2) for r in parent['residuals']]
 expected_private=['base0.T','pow0.quotient','base1.T','pow1.quotient','base2.T','pow2.quotient','radix.K','radix.L','radix_plus_one.K','radix_plus_one.L']
 removed={names.index(x) for x in expected_private};keep=[j for j in range(n) if j not in removed]
 removed_rows={i for i,p in enumerate(old) if any(removed&set(mon) for mon in p)}
 require(len(removed_rows)==10,'private row count')
 require(sorted(removed)==cert['removed_variables'] and sorted(removed_rows)==cert['removed_rows'],'deletion ledger')
 require(keep==cert['retained_old_indices'],'retained order')
 require(e['variables'][:-1]==[parent['variables'][j] for j in keep] and e['variables'][-1]=={'kind':'witness','name':'signed_reciprocal.z'},'coordinate metadata')
 require(e['domain']=='unrestricted integers','domain')
 require(e['reciprocal']['z_coordinate']==m-1,'quotient coordinate')
 require(e['reciprocal']['definition']=='sum_j(base_j * E_j * product_{l!=j} T_l) - z * product_l T_l','literal formula')
 ops=[v for v in operations['operations'] if v[0] not in removed_rows and v[1] not in removed_rows]
 require(ops==cert['retained_integer_row_operations'],'basis subsequence')
 rows=copy.deepcopy(old)
 for dst,src,a in ops:
  require(type(dst)is int and type(src)is int and 0<=dst<len(rows) and 0<=src<len(rows) and dst!=src and type(a)is int,'unit row addition')
  rows[dst]=sum_poly((1,rows[dst]),(a,rows[src]))
 outrows=[read_poly(r['terms'],m,2) for r in e['residuals']]
 require(len(outrows)==145,'retained row count')
 j=0
 for i,p in enumerate(rows):
  if i in removed_rows:continue
  lifted={tuple(keep[v] for v in mon):c for mon,c in outrows[j].items()}
  require(lifted==p and e['residuals'][j]['label']==parent['residuals'][i]['label'],'retained coefficients')
  j+=1
 V=lambda name:{(names.index(name),):1};one={():1};A=sum_poly((1,V('shared.A')),(1,one))
 labels=[r['label'] for r in parent['residuals']]
 specs=[('initial_growth','mul.1',1,'pow0.output',0,'index0.X_minus_AY','index0.Y','mul.460',0),('initial_B','choose0.output',0,'pow1.output',0,'index12.X_minus_AY','index12.Y','mul.645',1),('initial_BH','self_radix.BH',0,'pow2.output',-1,'index12.X_minus_AY','index12.Y','mul.645',1)]
 gg=e['reciprocal']['groups'];require([g['name'] for g in gg]==['initial_growth','initial_B','initial_BH','radix','radix_plus_one'],'block order')
 require([g['request_count'] for g in gg]==[1,1,1,3,11],'request ledger')
 decoded=[]
 for j,g in enumerate(gg):
  p={k:read_poly(g[k],m,{'base':1,'E':3,'T':2}[k]) for k in ['base','E','T']}
  lift=lambda q:{tuple(keep[v] for v in mon):c for mon,c in q.items()}
  b=lift(p['base']);E=lift(p['E']);T=lift(p['T'])
  wantT=sum_poly((2,product(A,b)),(-1,product(b,b)),(-1,one))
  require(T==wantT,'modulus semantics')
  if j<3:
   _,bn,bc,mn,mc,dn,yn,zn,zc=specs[j]
   wantb=sum_poly((1,V(bn)),(bc,one));mi=sum_poly((1,V(mn)),(mc,one));di=V(dn);yi=V(yn);zi=sum_poly((1,V(zn)),(zc,one))
   require(b==wantb,'singleton base')
   delta=sum_poly((1,mi),(-1,di),(-1,product(b,yi)))
   ay=sum_poly((1,zi),(-1,product(A,yi)));require(ay in old,'AY gate missing')
   tv=names.index(f'base{j}.T');qv=names.index(f'pow{j}.quotient')
   congruence=sum_poly((1,delta),(1,{tuple(sorted((tv,qv))):1}))
   require(congruence in old,'old singleton congruence')
   modrow=sum_poly((1,{(tv,):1}),(-1,T));require(modrow in old or {mon:-c for mon,c in modrow.items()} in old,'old singleton modulus')
   # Check the emitted E by its squared-error identity, not by the compiler's
   # H,S construction. The only remainder is the already retained AY gate.
   lhs=sum_poly((1,E),(-1,product(T,product(yi,yi))),(-1,product(delta,delta)))
   rhs=product(product(b,yi),ay);rhs={mon:2*c for mon,c in rhs.items()}
   require(lhs==rhs,'singleton square identity')
  else:
   name=g['name'];K=names.index(name+'.K');L=names.index(name+'.L');ar=old[labels.index(name+'.bilinear_aggregate')];br=old[labels.index(name+'.pooled_norm')]
   wantb=sum_poly((1,V('pow2.output')),((-1 if name=='radix' else 0),one));require(b==wantb,'radix base')
   left=sum_poly((1,E),(-1,product(T,{(L,):1})))
   right=sum_poly((1,br),(1,product(b,ar)))
   require(left==right,'old pool elimination identity')
  decoded.append(p)
 # Every old deleted coordinate must have been checked by one singleton or pool.
 require(sum(g['request_count'] for g in gg)==17,'total requests')
 # Exact degree: structural upper bound 24 plus independent finite differences
 # of the univariate restriction. This evaluates only ordinary integer gates.
 def total(t):
  x=[t]*m;rr=sum(eval_p(p,x)**2 for p in outrows);tt=[eval_p(p['T'],x) for p in decoded];v=0
  for j,p in enumerate(decoded):
   a=eval_p(p['base'],x)*eval_p(p['E'],x)
   for k,q in enumerate(tt):
    if k!=j:a*=q
   v+=a
  a=t
  for q in tt:a*=q
  return rr+(v-a)**2
 vals=[total(t) for t in range(25)]
 for _ in range(24):vals=[b-a for a,b in zip(vals,vals[1:])]
 require(vals==[factorial(24)*1156],'degree certificate')
 return {'variables':m,'residuals':146,'exact_degree':24,'leading_line_coefficient':1156,'source_rows_replayed':len(rows),'retained_row_operations':len(ops),'all_five_block_identities_checked':True}

def main():
 parent=json.loads((ROOT/'source/affine218.json').read_text());ops=json.loads((ROOT/'source/basis_operations.json').read_text());e=json.loads((ROOT/'equation.json').read_text());cert=json.loads((ROOT/'certificate.json').read_text());receipt=check(parent,ops,e,cert)
 cases=[]
 for name,edit in [('wrong_base',lambda t:t['reciprocal']['groups'][0]['base'][0].__setitem__(0,2*t['reciprocal']['groups'][0]['base'][0][0])),('wrong_E',lambda t:t['reciprocal']['groups'][2]['E'][0].__setitem__(0,2*t['reciprocal']['groups'][2]['E'][0][0])),('wrong_retained_row',lambda t:t['residuals'][0]['terms'][0].__setitem__(0,2*t['residuals'][0]['terms'][0][0])),('wrong_z',lambda t:t['reciprocal'].__setitem__('z_coordinate',0))]:
  t=copy.deepcopy(e);edit(t);c=copy.deepcopy(cert);c['output_sha256']=sha(t)
  try:check(parent,ops,t,c)
  except ValueError:cases.append(name)
  else:raise ValueError('accepted corruption: '+name)
 receipt['negative_controls_rejected']=cases;receipt['scope']='finite polynomial and artifact checks; unbounded arithmetic proof is separate';print(json.dumps(receipt,sort_keys=True,indent=2))
if __name__=='__main__':main()
