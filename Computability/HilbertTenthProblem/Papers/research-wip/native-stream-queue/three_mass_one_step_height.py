#!/usr/bin/env python3
"""Three pinned one-step mass clocks with height independent of the clock input.
Standard-library only. Historical Python is authenticated, never executed.
"""
import argparse, copy, hashlib, json, random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__: raise RuntimeError('Run without -O')
PINS={
 'three_mass_target_free_height.py':'7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49',
 'three_mass_target_free_height.json':'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830',
 'three_mass_target_free_height.md':'61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a',
 'three_mass_unbounded_endpoint_projection.py':'96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd',
 'three_mass_unbounded_endpoint_projection.json':'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457',
 'three_mass_unbounded_endpoint_projection.md':'8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c',
 'native_pell_factored_first_coefficient.py':'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'native_pell_factored_first_coefficient.json':'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'native_pell_factored_first_coefficient.md':'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528',
 'three_mass_unbounded_interface.py':'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a',
 'three_mass_unbounded_interface.json':'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e',
 'three_mass_unbounded_interface.md':'d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45',
 'residue_affine_packed_history.py':'d06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4',
 'residue_affine_packed_history.json':'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421',
 'residue_affine_packed_history.md':'0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882'}
VARIANTS=('clock_zero3','clock_nop','clock_positive3')
EXPECTED=((466,180,286,56,1192),(464,178,286,56,1192),(467,185,282,56,1192))
def need(c,m):
 if not c: raise ValueError(m)
def sha(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def ledger(rows,ends,parameters,aux):
 need(type(rows)is list and type(parameters)is list and type(aux)is list,'exact source containers')
 free=set(parameters+aux);need(len(free)==len(parameters)+len(aux),'disjoint ports')
 need(all(type(x)is str for x in free),'typed ports')
 ds={x:1 for x in free};deps={};c=Counter();used=set()
 for row in rows:
  need(type(row)is list and len(row)==4,'gate row');n,op,a,b=row
  need(type(n)is str and n not in ds and type(op)is str and op in ('+','-','*'),'fresh gate')
  need(all(type(v)is int or type(v)is str and v in ds for v in (a,b)),'closed exact operands')
  deg=lambda v:0 if type(v)is int else ds[v]
  ds[n]=deg(a)+deg(b) if op=='*' else max(deg(a),deg(b));deps[n]=(a,b);c['M' if op=='*' else 'A']+=1
  used.update(v for v in (a,b) if type(v)is str and v in free)
 live=set();todo=list(ends)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n in free:used.add(n);continue
  need(n in deps,'closed output')
  if n not in live:live.add(n);todo.extend(deps[n])
 need(live==set(deps) and used==free,'all gates and supplied ports live')
 return dict(operations=len(rows),M=c['M'],A=c['A'],positive_witnesses=len(aux),equations=len(ends)//2 if len(ends)>1 else None,degree_upper_bound=max(ds[n] if type(n)is str else 0 for n in ends),all_gates_live=True)

def authenticated(root):
 root=Path(__file__).resolve().parent if root is None else Path(root)
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'source pin: '+name)
 receipt=json.loads((root/'three_mass_target_free_height.json').read_text())
 forms=[f['packet'] for f in receipt['forms']]
 need([p['variant'] for p in forms]==['clock_incdec']+list(VARIANTS),'exact four predecessor forms, incdec excluded')
 return forms[1:]

def canonical_parent(variant='clock_zero3',*,root=None):
 need(type(variant)is str and variant in VARIANTS,'exact variant')
 return copy.deepcopy(authenticated(root)[VARIANTS.index(variant)])

def one_step_proof(mapping):
 K=mapping['K'];m=mapping['modulus'];initial=mapping['initial'];halt=mapping['halt'];trap=mapping['trap']
 need((K,m,initial,halt,trap)==(5,30,1,2,3),'three actual one-step control interfaces')
 need(len(mapping['table'])==m and len(mapping['clocks'])==m,'all fixed residue rows')
 transitions=[]
 for r,((a,d),(c,b)) in enumerate(zip(mapping['table'],mapping['clocks']),1):
  src=(r-1)%K+1;dest=(d-1)%K+1
  need(a==30 and a%K==0,'control independent of quotient')
  need(dest in (halt,trap) if src==initial else dest==trap,'initial halts or traps; all other controls trap')
  need(c==1152 and b==200+192*((r-1)//K),'actual uniform clock coefficients')
  transitions.append([r,src,dest])
 need(any(src==initial and dest==halt for r,src,dest in transitions),'nonempty accepting residue set')
 return {'residue_control_edges':transitions,'accepted_duration':1,'clock_word_at_acceptance':'1152*q+b_r','uniform_tick_bound':'1152*(h-1)+1160 = 1152*h+8','incdec_excluded':True}

def _rewrite(parent):
 p=copy.deepcopy(parent);rows=p['source'];pairs=p['comparisons'];d={n:(op,a,b) for n,op,a,b in rows}
 h=p['interfaces']['height'];proof=one_step_proof(p['mapping'])
 need(p['variant'] in VARIANTS and p['parameters']==['x','y','T'] and p['domains']=={'parameters':'natural','auxiliaries':'positive'} and len(pairs)==19,'same exact allowed interface')
 need(d['bridge_height_without_time']==('+','bridge_input','height_slack') and d[h]==('+','bridge_height_without_time','T'),'actual private two-addition height')
 need({n for n,o,a,b in rows if 'bridge_height_without_time' in (a,b)}=={h},'private height intermediate')
 need({n for n,o,a,b in rows if 'height_slack' in (a,b)}=={'bridge_height_without_time'},'sole slack consumer')
 need(all('bridge_height_without_time' not in pair and 'height_slack' not in pair for pair in pairs),'no private comparison use')
 new=[]
 for n,o,a,b in rows:
  if n=='bridge_height_without_time':continue
  new.append([n,'+','bridge_input','height_slack'] if n==h else [n,o,a,b])
 p['source']=new;p['polynomial_source']=new+copy.deepcopy(parent['polynomial_source'][len(rows):])
 p['historical_target_free_projection']=p.pop('projection')
 p['historical_target_free_projection_role']='Predecessor provenance only; its height includes T and is not the current height definition.'
 p['projection']={'same_supplied_coordinates':True,'same_coordinate_polynomial_identity':False,'full_polynomial_identity_under_signed_pullback':True,'signed_parent_pullback':{'height_slack':'height_slack-T'},'positive_parent_embedding':{'height_slack':'height_slack+T'},'unconditional_positive_pullback':False,'full_natural_zero_bijection_claimed':False,'represented_relation':'Same raw natural (x,y,T) relation for the three fixed one-step programs only. Incdec excluded.','removed_registers':['bridge_height_without_time'],'height_formula':'bridge_input+height_slack','height_minimum_on_domain':2,'clock_quotient_arithmetic_retained':True}
 p['one_step_control_proof']=proof;p['scope']='Three fixed programs zero3/nop/positive3, whose accepting paths have exactly one step. Same natural raw x/y/T, positive witnesses and exact physical clock. No general unbounded-runtime height removal or universal bound; incdec is excluded.'
 p['parent_pins']=copy.deepcopy(PINS)
 p['certificate_ledger']=ledger(new,[v for pair in pairs for v in pair],p['parameters'],p['auxiliaries']);p['polynomial_ledger']=ledger(p['polynomial_source'],[p['output']],p['parameters'],p['auxiliaries'])
 for key in ('certificate_ledger','polynomial_ledger'):
  a=parent[key];b=p[key];need((b['operations'],b['M'],b['A'])==(a['operations']-1,a['M'],a['A']-1),'complete one-addition saving')
  need(b['positive_witnesses']==a['positive_witnesses'] and b['degree_upper_bound']==a['degree_upper_bound'],'same witness count and upper degree')
 need(p['comparisons']==parent['comparisons'] and p['auxiliaries']==parent['auxiliaries'],'all comparisons and quotient witness retained')
 return p

def build(variant='clock_zero3',*,root=None):return _rewrite(canonical_parent(variant,root=root))
def rewrite(parent,*,root=None):
 need(type(parent)is dict and type(parent.get('variant'))is str,'parent packet')
 expected=canonical_parent(parent['variant'],root=root);need(exact(parent,expected),'canonical parent required');return _rewrite(expected)
def checked(packet,*,root=None):
 need(type(packet)is dict and type(packet.get('variant'))is str,'child packet')
 expected=build(packet['variant'],root=root);need(exact(packet,expected),'canonical child required');return expected

def run(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return e

def values_ok(p,values,signed):
 need(type(signed)is bool,'exact signed flag')
 need(type(values)is dict and set(values)==set(p['parameters']+p['auxiliaries']),'exact complete values')
 need(all(type(n)is str and type(v)is int for n,v in values.items()),'exact integer values')
 if not signed:need(all(values[n]>0 for n in p['auxiliaries']) and all(values[n]>=0 for n in p['parameters']),'positive witnesses and natural parameters')
def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);values_ok(p,values,signed);return run(p['polynomial_source'],values)[p['output']]
def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
def integer_pullback(packet,values,*,root=None):
 p=checked(packet,root=root);values_ok(p,values,True);return _pullback(p,values)
def _pullback(p,values):
 v=dict(values);v['height_slack']-=v['T'];return v

def embed_parent_assignment(packet,values,*,root=None):
 p=checked(packet,root=root);values_ok(p,values,False)
 v=dict(values);v['height_slack']+=v['T'];return v

def whole_proof(parent,p):
 # Expand the actual height cones after the stated affine substitution.
 variables=['x','y','T','height_slack'];zero=(0,)*4
 def add(a,b,sign=1):
  z=a.copy()
  for m,c in b.items():z[m]=z.get(m,0)+sign*c
  return {m:c for m,c in z.items() if c}
 def mul(a,b):
  z={}
  for m,c in a.items():
   for n,d in b.items():
    k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+c*d
  return {m:c for m,c in z.items() if c}
 h=p['interfaces']['height'];K=p['mapping']['K'];qh=p['mapping']['halt']
 def affine(rows,old):
  e={v:{tuple(int(j==i) for j in range(4)):1} for i,v in enumerate(variables)}
  if old:e['height_slack']=add(e['height_slack'],e['T'],-1)
  for n,op,a,b in rows:
   if (type(a)is int or a in e) and (type(b)is int or b in e):
    a={zero:a} if type(a)is int else e[a];b={zero:b} if type(b)is int else e[b]
    e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
   if n==h:break
  return e[h]
 oldheight=affine(parent['source'],True);newheight=affine(p['source'],False)
 expected={(1,0,0,0):K,(0,0,0,1):1,zero:p['mapping']['initial']}
 need(oldheight==newheight==expected,'actual height polynomial identity')
 atoms={}
 def intern(t):
  if t not in atoms:atoms[t]=len(atoms)
  return atoms[t]
 def execute(rows,old):
  e={n:intern(('input',n)) for n in p['parameters']+p['auxiliaries']}
  if old:e['height_slack']=intern(('-',e['height_slack'],e['T']))
  at=lambda v:intern(('constant',v)) if type(v)is int else e[v]
  for n,op,a,b in rows:e[n]=intern(('proved_height_cut',)) if n==h else intern((op,at(a),at(b)))
  return e
 a=execute(parent['polynomial_source'],True);b=execute(p['polynomial_source'],False)
 for l,r in p['comparisons']:need((a[l],a[r])==(b[l],b[r]),'every actual comparison operand')
 need(a[parent['output']]==b[p['output']],'whole actual finalizer graph identity')
 return {'affine_height_coefficients':[[list(m),c] for m,c in sorted(expected.items())],'retained_comparison_identities':19,'complete_polynomial_identity':True,'identity_requires_signed_slack_substitution':True}

# Finite outer witnesses, no materialization of native Pell coordinates.
def outer_fixture(p,x):
 mp=p['mapping'];K=mp['K'];m=mp['modulus'];table=mp['table'];clocks=mp['clocks'];path=[K*x+mp['initial']];ticks=[];qs=[];rs=[]
 for _ in range(6):
  q,r=divmod(path[-1]-1,m);a,d=table[r];c,b=clocks[r];qs.append(q);rs.append(r);ticks.append(c*q+b);path.append(a*q+d)
  if (path[-1]-1)%K+1==mp['halt']:break
  if (path[-1]-1)%K+1==mp['trap']:return None
 else:return None
 T=sum(ticks);y=(path[-1]-mp['halt'])//K+1
 h=1
 while h<=path[0] or h<=max(qs):h*=2
 # B constant comes from the actual paid radix gate.
 radix=next(row for row in p['source'] if row[1]=='*' and row[3]=='bridge_height_square');B=radix[2]*h*h
 length=len(qs);P=B**length;J=(P-1)//(B-1)
 pack=lambda xs:sum(v*B**i for i,v in enumerate(xs))
 E=[pack([int(r==j) for r in rs]) for j in range(m)];W=pack(qs)
 baseline=min(a for a,d in table);classes=sorted({a for a,d in table}-{baseline});Z=[pack([q if table[r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
 v={n:1 for n in p['auxiliaries']};v.update(x=x,y=y,T=T,quotient_hat=W+1,height_slack=h-path[0],global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+(pack(ticks)-T)//(B-1))
 v.update({f'edge{i}_hat':e+1 for i,e in enumerate(E)});v.update({f'product{i}_hat':z+1 for i,z in enumerate(Z)})
 need(all(v[n]>0 for n in p['auxiliaries']),'strict outer hats/slacks')
 e=run(p['source'],v)
 for l,r in [p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]]:need(e[l]==e[r],'three actual outer comparisons')
 # Original literal AND interfaces, recovered at their actual paid padding ports.
 H=(e['native__padded_A']-12)//16;M=(e['native__padded_B']-10)//16;A=(e['native__F3']-8)//16
 need(H&M==A,'actual joined AND lanes')
 need(length==1 and v['clock_quotient_hat']==1 and T==ticks[0] and 0<T<B-1,'actual one-step exact clock')
 need(e[p['interfaces']['height']]==h and e['bridge_target']==path[-1],'exact height and endpoint')
 return {'x':x,'y':y,'T':T,'steps':length,'height':h,'height_slack':v['height_slack'],'signed_target_free_parent_slack':v['height_slack']-T,'clock_quotient_hat':v['clock_quotient_hat'],'outer_and':True,'native_witnesses_materialized':False}

def clock_source_proof(p):
 # Recover the entire actual clock word as a linear polynomial in unhatted words.
 names=['quotient_hat']+[f'edge{i}_hat' for i in range(p['mapping']['modulus'])]
 zero=(0,)*len(names)
 e={v:{tuple(int(i==j) for i in range(len(names))):1} for j,v in enumerate(names)}
 def add(a,b,sign=1):
  z=a.copy()
  for m,c in b.items():z[m]=z.get(m,0)+sign*c
  return {m:c for m,c in z.items() if c}
 def mul(a,b):
  z={}
  for m,c in a.items():
   for n,d in b.items():
    k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+c*d
  return {m:c for m,c in z.items() if c}
 for n,o,a,b in p['source']:
  if (type(a)is int or a in e) and (type(b)is int or b in e):
   aa={zero:a} if type(a)is int else e[a];bb={zero:b} if type(b)is int else e[b]
   e[n]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
 lhs,rhs=p['comparisons'][-1];weights=[1152]+[b for c,b in p['mapping']['clocks']]
 expected={tuple(int(i==j) for i in range(len(names))):w for j,w in enumerate(weights)}
 expected[zero]=-sum(weights)
 need(e[lhs]==expected,'complete literal clock word, all hats and coefficients paid')
 d={n:(o,a,b) for n,o,a,b in p['source']}
 need(d[rhs][0]=='+' and d[rhs][2]=='T','retained clock adds T')
 prod=d[rhs][1];need(d[prod][0]=='*','retained clock quotient product')
 a,b=d[prod][1:];qh=a if d.get(a)==('-','clock_quotient_hat',1) else b
 bm=b if qh==a else a
 radix=next(n for n,o,a,b in p['source'] if o=='*' and b=='bridge_height_square')
 need(d.get(qh)==('-','clock_quotient_hat',1) and d.get(bm)==('-',radix,1),'retained exact clock quotient cone')
 return {'lhs_unhatted_coefficients':weights,'retained_clock_quotient_gates':[qh,prod,rhs],'clock_rhs':'(B-1)*(clock_quotient_hat-1)+T'}

def verify(root):
 root=Path(root);forms=[];counts=Counter();rng=random.Random(466464467)
 for variant,expected in zip(VARIANTS,EXPECTED):
  parent=canonical_parent(variant,root=root);p=rewrite(parent,root=root)
  proof=whole_proof(parent,p);cp=clock_source_proof(p)
  counts['complete_graph_proofs']+=1;counts['retained_comparison_identities']+=19;counts['clock_source_proofs']+=1
  led=p['polynomial_ledger'];need((led['operations'],led['M'],led['A'],len(p['auxiliaries']),led['degree_upper_bound'])==expected,'actual entire ledger')
  need(p['polynomial_source'][len(p['source']):]==parent['polynomial_source'][len(parent['source']):] and len(p['polynomial_source'])-len(p['source'])==56,'same fully paid nineteen-square finalizer')
  for i in range(16):
   v={n:rng.randrange(-3,4) for n in p['parameters']+p['auxiliaries']}
   if i>=12:v={n:Fraction(k,3) for n,k in v.items()};counts['rational_cases']+=1
   pv=_pullback(p,v);a=run(parent['polynomial_source'],pv);b=run(p['polynomial_source'],v)
   need(a[parent['output']]==b[p['output']],'whole evaluated signed identity');counts['whole_evaluations']+=1
   for l,r in p['comparisons']:need(a[l]-a[r]==b[l]-b[r],'all retained numeric residuals');counts['residual_evaluations']+=1
  for _ in range(8):
   v={n:rng.randrange(1,4) for n in p['auxiliaries']};v.update({n:rng.randrange(0,4) for n in p['parameters']})
   embedded=embed_parent_assignment(p,v,root=root);need(embedded['height_slack']>0 and integer_pullback(p,embedded,root=root)==v,'unconditional positive parent embedding')
   need(evaluate(p,embedded,root=root)==run(parent['polynomial_source'],v)[parent['output']],'embedding whole output');counts['positive_parent_embeddings']+=1
  C=next(row[2] for row in p['source'] if row[1]=='*' and row[3]=='bridge_height_square');m=p['mapping']['modulus']
  need(C==131072 and C>=max(4,m+1,1+max(a+d for a,d in p['mapping']['table'])),'actual radix and digit bound')
  for h in range(2,33):
   B=C*h*h
   need(B>m*h and all(a*(h-1)+d<B for a,d in p['mapping']['table']) and B-2*h>0 and 1152*h+8<B-1,'height-two typing and one-step clock bounds')
   for r,(c,b) in enumerate(p['mapping']['clocks']):
    for q in {0,h-1}:
     tick=c*q+b;need(0<tick<B-1,'positive bounded tick')
     for hat in range(1,4):
      T=tick-(B-1)*(hat-1);need((T>=0)==(hat==1) and (hat!=1 or T==tick),'natural T forces exact quotient one')
      counts['clock_residue_cases']+=1
  fixtures=[f for x in list(range(36))+[40,100] if (f:=outer_fixture(p,x)) is not None]
  for f in fixtures:need((f['y'],f['T'])==(f['x']+1,192*(f['x']+1)+8),'actual simple raw relation')
  counts['true_outer_and_fixtures']+=len(fixtures)
  v={n:1 for n in p['parameters']+p['auxiliaries']};v.update(x=0,y=0,T=0);e=run(p['source'],v)
  need(e[p['interfaces']['height']]==2 and all(e[n]>0 for n in ['native__padded_A','native__padded_B','native__F3','native__q']),'actual h2 pretyping boundary')
  counts['height_two_pretyping_cases']+=1
  fresh=build(variant,root=root);fresh['parent_pins'].clear();fresh['projection'].clear();need(exact(build(variant,root=root),p),'returned metadata copies');counts['metadata_copy_checks']+=1
  forms.append({'packet':p,'signed_graph_proof':proof,'clock_source_proof':cp,'outer_fixtures':fixtures})
 nop=next(f for f in forms if f['packet']['variant']=='clock_nop');negative=next(f for f in nop['outer_fixtures'] if f['x']==0)
 need((negative['y'],negative['T'],negative['height'],negative['height_slack'],negative['signed_target_free_parent_slack'])==(1,200,2,1,-199),'real nop outer inverse slack is negative')
 for bad in ['clock_incdec','bad',True,0,None]:
  try:build(bad,root=root)
  except ValueError:counts['rejected_variants']+=1
  else:raise ValueError('excluded variant accepted')
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':copy.deepcopy(PINS),'counts':dict(counts),'forms':forms,'negative_inverse_slack_fixture':negative,'scope':'Illustrative bounded three-source specialization only. Every accepting trajectory has one step; no unbounded-computation benefit, new universal source, or full positive-zero bijection. Incdec excluded. No huge native Pell tuple materialized; no broad public API audit claimed.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();result=verify(args.root)
 if args.expect:need(exact(result,json.loads(args.expect.read_text())),'exact typed saved receipt')
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','counts':result['counts']},sort_keys=True))
if __name__=='__main__':main()
