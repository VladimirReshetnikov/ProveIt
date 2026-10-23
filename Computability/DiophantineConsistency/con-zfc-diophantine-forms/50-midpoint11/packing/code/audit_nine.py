#!/usr/bin/env python3
"""Independent formula replay, exact identities, and exact degree certificate."""
import json,random
from nine_formula_helpers import ROOT,load,recval,evaluate,audit_graph,source,nine_rows,expected_nine,PORTS
from audit_parent_packing import add,mul

def lead(d,fix,p):
 ds=[];cs=[]
 for n in d['nodes']:
  k=n['kind']
  if k=='literal':degree,value=0,n['value']%p
  elif k=='fixed':degree,value=0,fix[n['name']]
  elif k=='variable':degree,value=1,1
  else:
   a,b=n['left'],n['right']
   if k=='mul':degree,value=ds[a]+ds[b],cs[a]*cs[b]%p
   else:
    degree=max(ds[a],ds[b]);value=((cs[a] if ds[a]==degree else 0)+(1 if k=='add' else -1)*(cs[b] if ds[b]==degree else 0))%p
  ds.append(degree);cs.append(value)
 return ds[d['output']],cs[d['output']]

def identities():
 def ring(n):
  one={(0,)*n:1};symbols=[]
  for i in range(n):
   e=[0]*n;e[i]=1;symbols.append({tuple(e):1})
  return one,symbols
 def sub(a,b):return add(a,b,-1)
 def sq(a):return mul(a,a)
 one,(A,C,E,G,H)=ring(5)
 D=add(mul(sub(sq(A),one),sq(C)),one)
 F=add(mul(sub(sq(A),one),sq(E)),one)
 I=add(mul(sub(sq(G),one),sq(H)),one)
 MD,MF,MI=mul(A,C),mul(A,E),mul(G,H)
 v1=mul(mul(MD,MF),MI);a1=mul(mul(D,F),I)
 delta=add(add(mul(mul(sub(sq(C),one),sq(MF)),sq(MI)),mul(mul(D,sub(sq(E),one)),sq(MI))),mul(mul(D,F),sub(sq(H),one)))
 assert sub(sub(sq(v1),a1),delta)=={}
 one,(E0,O,V0,V1,a0,a1)=ring(6);two=add(one,one)
 direct=sub(sq(sub(E0,mul(mul(O,V0),V1))),mul(sq(O),add(a0,mul(sq(V0),a1))))
 cert=sub(add(sub(sq(E0),mul(two,mul(mul(mul(E0,O),V0),V1))),mul(mul(sq(O),sq(V0)),sub(sq(V1),a1))),mul(sq(O),a0))
 assert sub(direct,cert)=={}
 return 2

def main():
 identity_count=identities();d=load('nine/generated/multitarget_nine_positive.json');dc=load('nine/generated/multitarget_nine_positive_degree_certificate.json')
 counts=audit_graph(d);audit_graph(dc);assert d['total_operations']==651 and len(d['variables'])==9
 assert d['W']==190 and d['degree']==30947584
 certificates=[];rng=random.Random(23102026);cases=0
 for p in [101,1009,1000003]:
  fixed={r['name']:recval(r['terms'],p) for r in d['coefficient_recipes']};fixed['base_floor']=pow(2,d['base_floor_exponent'],p)
  degree,lc=lead(dc,fixed,p);assert degree==30947584 and lc==pow(2,2050,p)!=0
  certificates.append({'prime':p,'degree':degree,'diagonal_leading_coefficient':lc,'equals_2_power_2050_mod_prime':True})
  rows=nine_rows(d,p)
  for j in range(35):
   x={v:rng.randint(-50,50) for v in d['variables']};out,named=evaluate(d,x,fixed,p)
   b=(fixed['base_floor']+x['epsilon']-1)%p;B=pow(b,3,p);src=source(b,x['g'],B,d['weights'],rows,p)
   for k in ['Dcode','ell','N0','N1','N','targets','Tcode','Jcode','Scode']:assert named[k]==src[k]
   expected,loc=expected_nine(d,x,src,p);assert out==expected
   assert out==evaluate(dc,x,fixed,p)[0]
   cases+=1
 dn=load('nine/generated/multitarget_nine_natural.json');audit_graph(dn);assert dn['total_operations']==654
 # The coefficient floor bound is checked exactly on the supplied bytes.
 M=2**d['coefficient_bound_power_of_two'];assert d['base_floor_exponent']==d['coefficient_bound_power_of_two']+12
 for r in d['coefficient_recipes']:
  exact=sum(t['coefficient']*__import__('math').prod(PORTS[k]**e for k,e in zip(PORTS,t['powers'])) for t in r['terms'])
  assert abs(exact)<M
 out={'status':'PASS','positive_operations':651,'nonnegative_operations':654,'variables':9,'exact_degree':30947584,'degree_certificates':certificates,'exact_general_polynomial_identities':identity_count,'modular_literal_source_finalizer_replays':cases,'complete_fixed_tuple_bit_lengths':{k:v.bit_length() for k,v in PORTS.items()},'fixed_coefficient_bound_exponent':d['coefficient_bound_power_of_two'],'base_floor_exponent':d['base_floor_exponent'],'scope':'Exact finite identities, coefficient bounds and degree certificate; modular replay is implementation evidence, not a proof of polynomial identity.'}
 (ROOT/'certificates/nine_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
