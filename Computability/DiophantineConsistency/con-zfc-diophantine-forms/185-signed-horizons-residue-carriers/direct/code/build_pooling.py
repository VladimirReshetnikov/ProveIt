#!/usr/bin/env python3
"""Compose source173 signed cofinal anchors with the inherited oriented pools.

The five-base pooling algebra is adapted from the Oriented Powers package.
New source bindings and the signed-horizon bootstrap are proved in
proofs/COMPOSITION_PROOF.md. Run the root verify.py for independent checks.
"""
import argparse,copy,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
SOURCE=ROOT/'sources/parent225.json'
PIN='fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56'
def canonical(a):return (json.dumps(a,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(a):return hashlib.sha256(canonical(a)).hexdigest()
def poly(a):return {tuple(m):c for c,m in a}
def serial(a):return [[c,list(m)] for m,c in sorted(a.items()) if c]
def con(c):return {():c} if c else {}
def var(i):return {(i,):1}
def add(a,b,c=1):
 o=dict(a)
 for m,v in b.items():
  o[m]=o.get(m,0)+c*v
  if not o[m]:del o[m]
 return o
def scale(a,c):return {m:c*v for m,v in a.items() if c*v}
def mul(a,b):
 o={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));o[k]=o.get(k,0)+c*d
 return {m:c for m,c in o.items() if c}
def prod(ps):
 o=con(1)
 for p in ps:o=mul(o,p)
 return o
def sq(a):return mul(a,a)
def coeff(a,j):
 o={}
 for m,c in a.items():
  k=list(m)
  if j in k:
   k.remove(j)
   if j in k:raise ValueError('Nonlinear distinguished variable')
   o[tuple(k)]=c
 return o
def atzero(a,js):return {m:c for m,c in a.items() if not(set(m)&set(js))}
def construct(parent,variant,anchor_certificate):
 n=len(parent['variables'])
 if n not in (219,220,221):raise ValueError('Expected source173 anchor')
 names=[v['name'] for v in parent['variables']]
 rows=[poly(r['terms']) for r in parent['residuals']]
 labels=[r['label'] for r in parent['residuals']]
 restores=[]
 rename_old=dict(anchor_certificate['original_to_final'])
 def ov(i):return var(rename_old[i])
 A=add(ov(142),con(1));groups=[]
 single=[]
 specs=[(0,149,150,ov(0),ov(2),ov(191),ov(192),ov(193)),(1,151,152,ov(4),ov(18),ov(182),ov(183),add(ov(184),con(1))),(2,153,154,ov(194),add(ov(102),con(-1)),ov(182),ov(183),add(ov(184),con(1)))]
 for j,t0,q0,base,m,D,Y,Z in specs:
  t,q=rename_old[t0],rename_old[q0]
  tr=[i for i,row in enumerate(rows) if (t,) in row and not any(q in mon for mon in row)]
  qr=[i for i,row in enumerate(rows) if any(q in mon for mon in row)]
  if len(tr)!=1 or len(qr)!=1:raise ValueError(('singleton binding',j,tr,qr))
  single.append((j,t,q,tr[0],qr[0],base,m,D,Y,Z))
 removed_vars=set();removed_rows=set()
 for j,t,q,rt,rq,base,m,D,Y,Z in single:
  T=add(add(scale(mul(A,base),2),sq(base),-1),con(-1))
  expected=add(var(t),T,-1)
  if rows[rt] not in (expected,scale(expected,-1)):raise ValueError(('T mismatch',j))
  delta=add(add(m,D,-1),mul(base,Y),-1)
  if rows[rq]!=add(delta,mul(var(t),var(q))):raise ValueError(('delta mismatch',j))
  E=add(add(sq(add(m,D,-1)),sq(Y),-1),scale(mul(mul(base,Y),add(add(m,D,-1),Z,-1)),-2))
  lhs=add(add(E,sq(delta),-1),mul(T,sq(Y)),-1)
  rhs=scale(mul(mul(base,Y),add(Z,mul(A,Y),-1)),2)
  if lhs!=rhs:raise ValueError('Power-square identity failed')
  groups.append(dict(name='single'+str(j),base=serial(base),T=serial(T),E=serial(E),Y_square_sum=serial(sq(Y)),delta=serial(delta),m=serial(m),D=serial(D),Y=serial(Y),Z=serial(Z),removed_modulus=t,removed_quotient=q,removed_rows=[rt,rq]))
  removed_vars.update([t,q]);removed_rows.update([rt,rq])
 for group in ('radix','radix_plus_one'):
  K=names.index(group+'.K');L=names.index(group+'.L')
  ia=labels.index(group+'.bilinear_aggregate');ib=labels.index(group+'.pooled_norm')
  ar,br=rows[ia],rows[ib]
  base=scale(coeff(br,K),-1);a=coeff(ar,L)
  ar0,br0=atzero(ar,[K,L]),atzero(br,[K,L])
  E=add(br0,mul(base,ar0));T=add(con(-1),mul(base,a),-1)
  if T!=add(add(scale(mul(A,base),2),sq(base),-1),con(-1)):raise ValueError('Pool T mismatch')
  if add(E,mul(T,var(L)),-1)!=add(br,mul(base,ar)):raise ValueError('Pool identity mismatch')
  groups.append(dict(name=group,base=serial(base),T=serial(T),E=serial(E),a=serial(a),aggregate_zero=serial(ar0),removed_K=K,removed_L=L,removed_rows=[ia,ib]))
  removed_vars.update([K,L]);removed_rows.update([ia,ib])
 if len(removed_vars)!=10 or len(removed_rows)!=10:raise ValueError('Removal count')
 for j,row in enumerate(rows):
  if j not in removed_rows and any(set(m)&removed_vars for m in row):raise ValueError(('Not private',j))
 retained=[j for j in range(n) if j not in removed_vars];rename={j:k for k,j in enumerate(retained)}
 def remap(p):return {tuple(rename[i] for i in m):c for m,c in p.items()}
 if variant=='all5':blocks=[dict(groups=[0,1,2,3,4],weights='base')]
 elif variant=='staged':blocks=[dict(groups=[0,1,2],weights='base'),dict(groups=[3,4],weights='one')]
 elif variant=='paired':blocks=[dict(groups=[0],weights='direct'),dict(groups=[1,2],weights='base'),dict(groups=[3,4],weights='one')]
 else:raise ValueError(variant)
 newvars=[copy.deepcopy(parent['variables'][j]) for j in retained]
 outrows=[dict(label=parent['residuals'][j]['label'],terms=serial(remap(row))) for j,row in enumerate(rows) if j not in removed_rows]
 newgroups=[]
 for g in groups:
  h=copy.deepcopy(g)
  for field in ('base','T','E','Y_square_sum','delta','m','D','Y','Z','a','aggregate_zero'):
   if field in h:h[field]=serial(remap(poly(h[field])))
  newgroups.append(h)
 witness_cert=[]
 for bi,block in enumerate(blocks):
  zi=len(newvars);newvars.append({'kind':'oriented_pool','name':'oriented.z'+str(bi)})
  block['quotient_index']=zi
  Ts=[poly(newgroups[j]['T']) for j in block['groups']];R={}
  for at,j in enumerate(block['groups']):
   g=newgroups[j];weight=poly(g['base']) if block['weights']=='base' else con(1)
   R=add(R,prod([weight,poly(g['E'])]+[p for i,p in enumerate(Ts) if i!=at]))
  if block['weights']=='direct':
   R=add(poly(newgroups[block['groups'][0]]['delta']),mul(var(zi),Ts[0]))
  else:R=add(R,mul(var(zi),prod(Ts)),-1)
  outrows.append({'label':'oriented.pool'+str(bi),'terms':serial(R)})
  witness_cert.append({'block':bi,'maximum_degree':max(map(len,R)),'expanded_residual_terms':len(R)})
 equation={'schema':'conzfc-oriented-pools-v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':variant,'parent_equation_sha256':digest(parent),'variables':newvars,'residuals':outrows}
 cert={'schema':'oriented-pools-certificate-v1','parent_byte_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'parent_canonical_sha256':digest(parent),'equation_sha256':digest(equation),'restoring_row_operations':restores,'removed_variables':sorted(removed_vars),'removed_rows':sorted(removed_rows),'retained_old_indices':retained,'A':serial(remap(A)),'groups':newgroups,'blocks':blocks,'finite_claim':'Explicit residual identities; semantic equivalence uses oriented-pool theorem and inherited bootstrap.'}
 met={'variables':len(newvars),'residuals':len(outrows),'degree':2*max(len(m) for r in outrows for c,m in r['terms']),'maximum_residual_degree':max(len(m) for r in outrows for c,m in r['terms']),'literal_residual_terms':sum(len(r['terms']) for r in outrows),'residual_coefficient_height':max(abs(c) for r in outrows for c,m in r['terms']),'all_coordinates_used':set(i for r in outrows for c,m in r['terms'] for i in m)==set(range(len(newvars))),'pool_details':witness_cert,'collected_polynomial_terms':None,'collected_polynomial_height':None}
 return equation,cert,met
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--anchor',type=int,default=221);parser.add_argument('--linear-horizon',action='store_true');parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
 source=ROOT/'upstream173'/'source'/('anchor'+str(args.anchor))
 global SOURCE
 SOURCE=source/'equation.json'
 parent=json.loads(SOURCE.read_bytes());anchor_certificate=json.loads((source/'certificate.json').read_text())
 results=[]
 if args.linear_horizon:
  ri=next(i for i,r in enumerate(parent['residuals']) if r['label']=='cofinal.horizon')
  vi=next(i for i,v in enumerate(parent['variables']) if v['name']=='cofinal.horizon_root')
  tmin=128 if args.anchor==221 else 16
  parent['residuals'][ri]['terms']=serial(add(add(var(0),scale(var(vi),-2*tmin)),con(-tmin)))
  parent['variables'][vi]['name']='cofinal.horizon_parameter'
  parent['schema']='conzfc-signed-cofinal-anchor-v1'
  parent['semantic_transform']='t = tmin*(2*z+1); positivity recovered from powers'
  args.output.mkdir(parents=True,exist_ok=True)
  (args.output/'signed_anchor_parent.json').write_bytes(canonical(parent))
 for variant in ('all5','staged','paired'):
  e,c,m=construct(parent,variant,anchor_certificate);dest=args.output/variant;dest.mkdir(parents=True,exist_ok=True)
  for f,obj in [('equation.json',e),('certificate.json',c),('metrics.json',m)]: (dest/f).write_bytes(canonical(obj))
  results.append({'variant':variant,**m})
 print(json.dumps(results,indent=2))
if __name__=='__main__':main()
