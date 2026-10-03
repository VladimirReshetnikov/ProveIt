#!/usr/bin/env python3
"""Four pinned unbounded mass-clock sources with target-free height.
Standard-library only. Historical Python is authenticated, never executed.
"""
import argparse, copy, hashlib, json, random, tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__: raise RuntimeError('Run without -O')
PINS={
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
VARIANTS=('clock_incdec','clock_zero3','clock_nop','clock_positive3')
EXPECTED=((592,235,357,58,2344),(467,180,287,56,1192),(465,178,287,56,1192),(468,185,283,56,1192))
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
 receipt=json.loads((root/'three_mass_unbounded_endpoint_projection.json').read_text())
 forms=[f['packet'] for f in receipt['forms']]
 need([p['variant'] for p in forms]==list(VARIANTS),'exact four source forms')
 return forms

def canonical_parent(variant='clock_incdec',*,root=None):
 need(type(variant)is str and variant in VARIANTS,'exact variant')
 return copy.deepcopy(authenticated(root)[VARIANTS.index(variant)])

def _rewrite(parent):
 p=copy.deepcopy(parent);rows=p['source'];pairs=p['comparisons'];d={n:(op,a,b) for n,op,a,b in rows}
 h=p['interfaces']['height'];K=p['mapping']['K'];qh=p['mapping']['halt'];initial=p['mapping']['initial']
 need(type(K)is int and K==5 and initial==1 and qh in (2,3),'actual fixed program constants')
 need(p['parameters']==['x','y','T'] and p['domains']=={'parameters':'natural','auxiliaries':'positive'} and len(pairs)==19,'same natural/positive interface and all rows')
 need(d['bridge_input_scaled']==('*',K,'x') and d['bridge_input']==('+','bridge_input_scaled',initial),'literal input')
 need(d['bridge_final_scaled']==('*',K,'y') and d['bridge_target']==('+','bridge_final_scaled',qh-K),'literal target')
 h0=d['bridge_height_without_time'][1]
 need(d[h0]==('+','bridge_input','bridge_target'),'actual endpoint sum')
 need(d['bridge_height_without_time']==('+',h0,'height_slack') and d['endpoint_raised_height']==('+','bridge_height_without_time',K) and d[h]==('+','endpoint_raised_height','T'),'actual four-addition height')
 for n,users in [(h0,{'bridge_height_without_time'}),('bridge_height_without_time',{'endpoint_raised_height'}),('endpoint_raised_height',{h}),('height_slack',{'bridge_height_without_time'})]:
  need({dest for dest,op,a,b in rows if n in (a,b)}==users,'private height consumer closure')
  need(all(n not in pair for pair in pairs),'private height comparison closure')
 new=[]
 for n,op,a,b in rows:
  if n in (h0,'endpoint_raised_height'):continue
  if n=='bridge_height_without_time':new.append([n,'+','bridge_input','height_slack'])
  elif n==h:new.append([n,'+','bridge_height_without_time','T'])
  else:new.append([n,op,a,b])
 # Keep the literal complete finalizer and every comparison in its old order.
 p['source']=new;p['polynomial_source']=new+copy.deepcopy(parent['polynomial_source'][len(rows):])
 p['historical_endpoint_projection']=p.pop('projection')
 p['historical_endpoint_projection_role']='Predecessor provenance only; its positive parent-slice map is not a map for the current packet.'
 p['projection']={'same_supplied_coordinates':True,'same_coordinate_polynomial_identity':False,'full_polynomial_identity_under_signed_pullback':True,'signed_parent_pullback':{'height_slack':f'height_slack-{K}*y-{qh}'},'unconditional_positive_pullback':False,'full_natural_zero_bijection_claimed':False,'represented_relation':'Same fixed-program raw natural (x,y,T) first-halt clock relation by direct soundness and fresh-height completeness.','removed_registers':[h0,'endpoint_raised_height'],'height_formula':'bridge_input+T+height_slack','height_minimum_on_domain':2}
 p['parent_pins']=copy.deepcopy(PINS)
 p['certificate_ledger']=ledger(new,[v for pair in pairs for v in pair],p['parameters'],p['auxiliaries'])
 p['polynomial_ledger']=ledger(p['polynomial_source'],[p['output']],p['parameters'],p['auxiliaries'])
 for key in ('certificate_ledger','polynomial_ledger'):
  a=parent[key];b=p[key];need((b['operations'],b['M'],b['A'])==(a['operations']-2,a['M'],a['A']-2),'complete two-addition saving')
  need(b['positive_witnesses']==a['positive_witnesses'] and b['degree_upper_bound']==a['degree_upper_bound'],'witness count and propagated degree')
 need(p['comparisons']==parent['comparisons'] and p['auxiliaries']==parent['auxiliaries'],'unchanged full constraints and coordinates')
 return p

def build(variant='clock_incdec',*,root=None):return _rewrite(canonical_parent(variant,root=root))
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
 v=dict(values);v['height_slack']-=p['mapping']['K']*v['y']+p['mapping']['halt'];return v

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
  if old:e['height_slack']=add(add(e['height_slack'],mul({zero:K},e['y']),-1),{zero:qh},-1)
  for n,op,a,b in rows:
   if (type(a)is int or a in e) and (type(b)is int or b in e):
    a={zero:a} if type(a)is int else e[a];b={zero:b} if type(b)is int else e[b]
    e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
   if n==h:break
  return e[h]
 oldheight=affine(parent['source'],True);newheight=affine(p['source'],False)
 expected={(1,0,0,0):K,(0,0,1,0):1,(0,0,0,1):1,zero:p['mapping']['initial']}
 need(oldheight==newheight==expected,'actual height polynomial identity')
 atoms={}
 def intern(t):
  if t not in atoms:atoms[t]=len(atoms)
  return atoms[t]
 def execute(rows,old):
  e={n:intern(('input',n)) for n in p['parameters']+p['auxiliaries']}
  if old:e['height_slack']=intern(('-',intern(('-',e['height_slack'],intern(('*',intern(('constant',K)),e['y'])))),intern(('constant',qh))))
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
 while h<=path[0]+T or h<=max(qs):h*=2
 # B constant comes from the actual paid radix gate.
 radix=next(row for row in p['source'] if row[1]=='*' and row[3]=='bridge_height_square');B=radix[2]*h*h
 length=len(qs);P=B**length;J=(P-1)//(B-1)
 pack=lambda xs:sum(v*B**i for i,v in enumerate(xs))
 E=[pack([int(r==j) for r in rs]) for j in range(m)];W=pack(qs)
 baseline=min(a for a,d in table);classes=sorted({a for a,d in table}-{baseline});Z=[pack([q if table[r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
 v={n:1 for n in p['auxiliaries']};v.update(x=x,y=y,T=T,quotient_hat=W+1,height_slack=h-path[0]-T,global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+(pack(ticks)-T)//(B-1))
 v.update({f'edge{i}_hat':e+1 for i,e in enumerate(E)});v.update({f'product{i}_hat':z+1 for i,z in enumerate(Z)})
 need(all(v[n]>0 for n in p['auxiliaries']),'strict outer hats/slacks')
 e=run(p['source'],v)
 for l,r in [p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]]:need(e[l]==e[r],'three actual outer comparisons')
 # Original literal AND interfaces, recovered at their actual paid padding ports.
 H=(e['native__padded_A']-12)//16;M=(e['native__padded_B']-10)//16;A=(e['native__F3']-8)//16
 need(H&M==A,'actual joined AND lanes')
 need(e[p['interfaces']['height']]==h and e['bridge_target']==path[-1],'exact height and endpoint')
 return {'x':x,'y':y,'T':T,'steps':length,'height':h,'height_slack':v['height_slack'],'signed_endpoint_parent_slack':v['height_slack']-K*y-mp['halt'],'signed_coefficient_parent_slack':v['height_slack']-path[-1],'outer_and':True,'native_witnesses_materialized':False}

def verify(root):
 root=Path(root);counts=Counter();forms=[];rng=random.Random(592467465468)
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['rejections']+=1
  else:raise ValueError('unsupported caller accepted')
 for variant,expected in zip(VARIANTS,EXPECTED):
  parent=canonical_parent(variant,root=root);p=rewrite(parent,root=root);proof=whole_proof(parent,p)
  counts['whole_source_proofs']+=1;counts['formal_retained_comparisons']+=19
  led=p['polynomial_ledger'];need((led['operations'],led['M'],led['A'],len(p['auxiliaries']),led['degree_upper_bound'])==expected,'complete actual ledger')
  for i in range(32):
   v={n:rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   if i<8:v.update({n:rng.randrange(0,4) for n in p['parameters']})
   else:v={n:rng.randrange(-3,4) for n in v}
   if i>=24:v={n:Fraction(k,3) for n,k in v.items()};counts['rational_identities']+=1
   pv=_pullback(p,v);a=run(parent['polynomial_source'],pv);b=run(p['polynomial_source'],v)
   need(a[parent['output']]==b[p['output']],'full numeric signed pullback');counts['complete_evaluations']+=1
   for l,r in p['comparisons']:need(a[l]-a[r]==b[l]-b[r],'complete retained numeric row');counts['residual_evaluations']+=1
   if i<24:
    need(evaluate(p,v,signed=i>=8,root=root)==b[p['output']],'public evaluation')
    need(integer_pullback(p,v,root=root)==pv,'public signed map');counts['public_map_evaluations']+=1
  fixtures=[f for x in list(range(36))+[40,100] if (f:=outer_fixture(p,x)) is not None];counts['genuine_outer_fixtures']+=len(fixtures)
  v={n:1 for n in p['parameters']+p['auxiliaries']};v.update(x=0,y=0,T=0);e=run(p['source'],v)
  need(e[p['interfaces']['height']]==2 and e['bridge_target']<=0,'exact h2/y0 boundary')
  need(all(e[n]>0 for n in ('native__padded_A','native__padded_B','native__F3','native__q')),'native pretyping positivity at h2');counts['height_two_boundaries']+=1
  evaluate(p,v,root=root)
  # All actual fixed constants meet the general small-height proof margins.
  mp=p['mapping'];m=mp['modulus'];g=len({a for a,d in mp['table']})-1
  C=next(row[2] for row in p['source'] if row[1]=='*' and row[3]=='bridge_height_square')
  need(C>=max(4,m+1,max(a+d for a,d in mp['table'])+1,2384*m+2) and C&(C-1)==0,'actual dyadic C')
  for hh in range(2,65):
   B=C*hh*hh
   need(B>m*hh and all(a*(hh-1)+d<B for a,d in mp['table']) and (B-2*hh)-g>0 and B-1-2384*m*hh*hh>=7,'digit/global-slack/clock margins including h2');counts['height_margin_checks']+=1
  for key in p:
   bad=copy.deepcopy(p);del bad[key];reject(lambda bad=bad:checked(bad,root=root))
  for key in ['source','polynomial_source','comparisons','auxiliaries','parameters']:
   bad=copy.deepcopy(p);bad[key]=tuple(bad[key]);reject(lambda bad=bad:checked(bad,root=root))
  for key in ['source','comparisons','projection','historical_endpoint_projection','mapping','degree','parent_pins']:
   bad=copy.deepcopy(p);bad[key].clear();need(exact(build(variant,root=root),p),'returned copies');counts['copies']+=1
  q=polynomial_source(p,root=root);q[0][2]=999;need(polynomial_source(p,root=root)==p['polynomial_source'],'source accessor copy');counts['copies']+=1
  pv=integer_pullback(p,v,root=root);pv['x']=999;need(v['x']==0 and integer_pullback(p,v,root=root)['x']==0,'map copy');counts['copies']+=1
  pp=canonical_parent(variant,root=root);pp['source'][0][2]=999;reject(lambda:rewrite(pp,root=root));need(canonical_parent(variant,root=root)==parent,'parent copy');counts['copies']+=1
  bad=copy.deepcopy(p);bad['polynomial_ledger']['M']=float(bad['polynomial_ledger']['M']);reject(lambda:checked(bad,root=root))
  for flag in [0,1,None]:reject(lambda flag=flag:evaluate(p,v,signed=flag,root=root))
  for value in [True,1.0,Fraction(1),None]:
   bad=v.copy();bad['x']=value;reject(lambda bad=bad:evaluate(p,bad,signed=True,root=root));reject(lambda bad=bad:integer_pullback(p,bad,root=root))
  for name in ['x',p['auxiliaries'][0]]:
   bad=v.copy();bad[name]=-1;reject(lambda bad=bad:evaluate(p,bad,root=root))
  for bad in [dict(v,extra=1),{n:k for n,k in v.items() if n!='x'}]:reject(lambda bad=bad:evaluate(p,bad,root=root))
  forms.append({'packet':p,'proof':proof,'outer_fixtures':fixtures})
 nop=next(f for f in forms if f['packet']['variant']=='clock_nop');negative=next(f for f in nop['outer_fixtures'] if f['x']==40)
 need((negative['y'],negative['T'],negative['height'],negative['height_slack'],negative['signed_endpoint_parent_slack'],negative['signed_coefficient_parent_slack'])==(41,7880,8192,111,-96,-91),'actual negative inverse-slack fixture')
 counts['negative_parent_slack_fixtures']+=1
 for variant in [None,0,True,'clock_bad']:reject(lambda variant=variant:build(variant,root=root))
 # Every canonical entry point reauthenticates every pinned artifact after warming.
 with tempfile.TemporaryDirectory() as tmp:
  for name in PINS:Path(tmp,name).write_bytes(Path(root,name).read_bytes())
  p=build(root=tmp);parent=canonical_parent(root=tmp);v={n:1 for n in p['parameters']+p['auxiliaries']}
  calls=[lambda:build(root=tmp),lambda:canonical_parent(root=tmp),lambda:checked(p,root=tmp),lambda:rewrite(parent,root=tmp),lambda:polynomial_source(p,root=tmp),lambda:evaluate(p,v,root=tmp),lambda:integer_pullback(p,v,root=tmp)]
  for call in calls:call()
  for name in PINS:
   path=Path(tmp,name);raw=path.read_bytes();path.write_bytes(raw+b'\n')
   for call in calls:reject(call);counts['warm_pin_checks']+=1
   path.write_bytes(raw)
 import subprocess,sys
 result=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--help'],capture_output=True,text=True)
 need(result.returncode!=0 and 'Run without -O' in result.stderr,'optimized-interpreter guard');counts['optimized_interpreter_rejections']+=1
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':copy.deepcopy(PINS),'counts':dict(counts),'forms':forms,'negative_inverse_slack_fixture':negative,'scope':'Four complete fixed-program unbounded clock sources; signed graph identity and separately proved equality of represented raw triples, not a positive full-zero bijection. Native Pell witnesses are not materialized.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();result=verify(args.root)
 if args.expect:need(exact(result,json.loads(args.expect.read_text())),'exact typed saved receipt')
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','counts':result['counts']},sort_keys=True))
if __name__=='__main__':main()
