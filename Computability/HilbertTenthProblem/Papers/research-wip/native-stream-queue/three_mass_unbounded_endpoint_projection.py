#!/usr/bin/env python3
"""Four pinned unbounded mass-clock sources: eliminate the positive output alias.
Standard-library only. Historical Python is authenticated, never executed.
"""
import argparse, copy, hashlib, json, random, tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__: raise RuntimeError('Run without -O')
PINS={
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
EXPECTED=((594,235,359,58,2344),(469,180,289,56,1192),(467,178,289,56,1192),(470,185,285,56,1192))
def need(c,m):
 if not c: raise ValueError(m)
def sha(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def authenticated(root):
 root=Path(__file__).resolve().parent if root is None else Path(root)
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'source pin: '+name)
 receipt=json.loads((root/'native_pell_factored_first_coefficient.json').read_text())
 forms=[f['packet'] for f in receipt['forms'] if f['variant'].startswith('clock_')]
 need([p['variant'] for p in forms]==list(VARIANTS),'exact four source forms')
 return forms

def sos(rows,pairs):
 rows=copy.deepcopy(rows)
 for i,(a,b) in enumerate(pairs):rows.extend([[f'ep_res{i}','-',a,b],[f'ep_sq{i}','*',f'ep_res{i}',f'ep_res{i}']])
 out='ep_sq0'
 for i in range(1,len(pairs)):
  n=f'ep_sum{i}';rows.append([n,'+',out,f'ep_sq{i}']);out=n
 return rows,out

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

def canonical_parent(variant='clock_incdec',*,root=None):
 need(type(variant)is str and variant in VARIANTS,'exact variant')
 return copy.deepcopy(authenticated(root)[VARIANTS.index(variant)])

def _rewrite(parent):
 rows=parent['source'];pairs=parent['comparisons'];d={n:(op,a,b) for n,op,a,b in rows}
 mapping=parent['parent_metadata']['mapping'];K=mapping['K'];halt=mapping['halt']
 need(type(K)is int and 1<=mapping['initial']<=K and 1<=halt<=K and mapping['initial']!=halt,'nonempty first-halt interface')
 need(parent['parameters']==['x','y','T'] and parent['domains']=={'parameters':'natural','auxiliaries':'positive'},'inherited domains')
 need(pairs[-1]==['final_positive','y'] and len(pairs)==20,'sole endpoint equality')
 need(d['bridge_final_minus_one']==('-', 'final_positive',1) and d['bridge_final_scaled']==('*',K,'bridge_final_minus_one') and d['bridge_target']==('+','bridge_final_scaled',halt),'literal endpoint cone')
 users=lambda v:{n for n,op,a,b in rows if v in (a,b)}
 need(users('final_positive')=={'bridge_final_minus_one'},'private positive endpoint')
 need(users('bridge_final_minus_one')=={'bridge_final_scaled'} and users('bridge_final_scaled')=={'bridge_target'},'private endpoint cone')
 h=next(n for n,op,a,b in rows if (op,a,b)==('+','bridge_height_without_time','T'))
 need(users('height_slack')=={'bridge_height_without_time'} and users('bridge_height_without_time')=={h},'private height slack')
 need(not any(v in pair for pair in pairs[:-1] for v in ['final_positive','bridge_final_minus_one','bridge_final_scaled','height_slack','bridge_height_without_time']),'private comparison closure')
 new=[]
 for row in rows:
  n,op,a,b=row
  if n=='bridge_final_minus_one':continue
  if n=='bridge_final_scaled':new.append([n,'*',K,'y'])
  elif n=='bridge_target':new.append([n,'+','bridge_final_scaled',halt-K])
  elif n==h:
   new.extend([['endpoint_raised_height','+','bridge_height_without_time',K],[n,'+','endpoint_raised_height','T']])
  else:new.append(row[:])
 aux=[n for n in parent['auxiliaries'] if n!='final_positive'];pairs=copy.deepcopy(pairs[:-1]);full,out=sos(new,pairs)
 p=dict(variant=parent['variant'],source=new,comparisons=pairs,polynomial_source=full,output=out,parameters=parent['parameters'][:],auxiliaries=aux,domains=copy.deepcopy(parent['domains']),mapping=copy.deepcopy(mapping),interfaces={'height':h,'input':'bridge_input','target':'bridge_target'},
  coefficient_transfer=copy.deepcopy(parent['transfer']),coefficient_transfer_scope='Unchanged coefficient identity only; parent whole-source digest is historical.',
  degree={'upper_bound':parent['degree']['upper_bound'],'exact_degree':None,'basis':'Actual source propagation; no exact-degree claim'},
  projection={'removed_positive_coordinate':'final_positive','removed_comparison':['final_positive','y'],'integer_pullback':{'final_positive':'y','height_slack':f'height_slack+{K}'},'full_polynomial_identity_under_pullback':True,'same_coordinate_polynomial_identity':False,'natural_zero_image':f'Parent zeros with height_slack>{K}','represented_relation':'Same fixed-program first-halt raw (x,y,T) relation; fresh larger history/native witnesses may be needed in reverse.'},
  scope='Four fixed finite programs, arbitrary existential runtime, natural raw x/y/T and positive auxiliaries. No universal ordinary-input decoder or numerical universal bound.',parent_pins=copy.deepcopy(PINS))
 p['certificate_ledger']=ledger(new,[v for pair in pairs for v in pair],p['parameters'],aux)
 p['polynomial_ledger']=ledger(full,[out],p['parameters'],aux)
 a=parent['polynomial_ledger'];b=p['polynomial_ledger']
 need((b['operations'],b['M'],b['A'])==(a['operations']-3,a['M']-1,a['A']-2),'complete saving')
 need(len(pairs)==19 and len(aux)==len(parent['auxiliaries'])-1,'complete interface reduction')
 need(b['degree_upper_bound']==p['degree']['upper_bound'],'propagated degree')
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
 v=dict(values);v['final_positive']=v['y'];v['height_slack']+=p['mapping']['K'];return v

def whole_proof(parent,p):
 # Exact affine coefficients establish the two shared cuts; structural interning
 # then proves every retained comparison and the complete SOS, with last square0.
 variables=['x','y','T','height_slack'];zero=(0,)*4
 def add(a,b,sgn=1):
  z=a.copy()
  for m,c in b.items():z[m]=z.get(m,0)+sgn*c
  return {m:c for m,c in z.items() if c}
 def mul(a,b):
  z={}
  for m,c in a.items():
   for n,d in b.items():
    k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+c*d
  return {m:c for m,c in z.items() if c}
 def affine(rows,old):
  e={v:{tuple(int(j==i) for j in range(4)):1} for i,v in enumerate(variables)}
  if old:e['final_positive']=e['y'];e['height_slack']=add(e['height_slack'],{zero:p['mapping']['K']})
  for n,op,a,b in rows:
   if (type(a)is int or a in e) and (type(b)is int or b in e):
    a={zero:a} if type(a)is int else e[a];b={zero:b} if type(b)is int else e[b]
    e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
   if n==p['interfaces']['height']:break
  return e
 a=affine(parent['source'],True);b=affine(p['source'],False)
 cuts=['bridge_target',p['interfaces']['height']]
 need(all(a[n]==b[n] for n in cuts),'exact complete affine cuts')
 atoms={}
 def intern(t):
  if t not in atoms:atoms[t]=len(atoms)
  return atoms[t]
 z=intern(('constant',0));one=intern(('constant',1))
 def opid(op,a,b):
  if op=='-' and a==b:return z
  if op=='+' and a==z:return b
  if op in ('+','-') and b==z:return a
  if op=='*' and z in (a,b):return z
  if op=='*' and a==one:return b
  if op=='*' and b==one:return a
  return intern((op,a,b))
 def execute(rows,old):
  e={n:intern(('input',n)) for n in p['parameters']+p['auxiliaries']}
  if old:
   e['final_positive']=e['y'];e['height_slack']=opid('+',e['height_slack'],intern(('constant',p['mapping']['K'])))
  at=lambda v:intern(('constant',v)) if type(v)is int else e[v]
  for n,op,a,b in rows:e[n]=intern(('proved_affine_cut',n)) if n in cuts else opid(op,at(a),at(b))
  return e
 a=execute(parent['polynomial_source'],True);b=execute(p['polynomial_source'],False)
 at=lambda e,v:intern(('constant',v)) if type(v)is int else e[v]
 for i,(l,r) in enumerate(p['comparisons']):
  need((at(a,l),at(a,r))==(at(b,l),at(b,r)),'all retained operands')
 need(a[parent['output']]==b[p['output']],'entire final polynomial identity')
 return {'affine_cuts':2,'retained_comparison_identities':19,'whole_polynomial_identity':True}

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
 while h<=path[0]+K*y+mp['halt']+T or h<=max(qs):h*=2
 # B constant comes from the actual paid radix gate.
 radix=next(row for row in p['source'] if row[1]=='*' and row[3]=='bridge_height_square');B=radix[2]*h*h
 length=len(qs);P=B**length;J=(P-1)//(B-1)
 pack=lambda xs:sum(v*B**i for i,v in enumerate(xs))
 E=[pack([int(r==j) for r in rs]) for j in range(m)];W=pack(qs)
 baseline=min(a for a,d in table);classes=sorted({a for a,d in table}-{baseline});Z=[pack([q if table[r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
 v={n:1 for n in p['auxiliaries']};v.update(x=x,y=y,T=T,quotient_hat=W+1,height_slack=h-path[0]-K*y-mp['halt']-T,global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+(pack(ticks)-T)//(B-1))
 v.update({f'edge{i}_hat':e+1 for i,e in enumerate(E)});v.update({f'product{i}_hat':z+1 for i,z in enumerate(Z)})
 need(all(v[n]>0 for n in p['auxiliaries']),'strict outer hats/slacks')
 e=run(p['source'],v)
 for l,r in [p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]]:need(e[l]==e[r],'three actual outer comparisons')
 # Original literal AND interfaces, recovered at their actual paid padding ports.
 H=(e['native__padded_A']-12)//16;M=(e['native__padded_B']-10)//16;A=(e['native__F3']-8)//16
 need(H&M==A,'actual joined AND lanes')
 need(e[p['interfaces']['height']]==h and e['bridge_target']==path[-1],'exact height and endpoint')
 return {'x':x,'y':y,'T':T,'steps':length,'height':h,'height_slack':v['height_slack'],'outer_and':True,'native_witnesses_materialized':False}

def verify(root):
 counts=Counter();forms=[];rng=random.Random(594469467470)
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['rejections']+=1
  else:raise ValueError('unsupported caller accepted')
 for variant,expected in zip(VARIANTS,EXPECTED):
  parent=canonical_parent(variant,root=root);p=build(variant,root=root);proof=whole_proof(parent,p);counts['whole_source_proofs']+=1;counts['formal_retained_rows']+=19
  led=p['polynomial_ledger'];need((led['operations'],led['M'],led['A'],len(p['auxiliaries']),led['degree_upper_bound'])==expected,'whole counted form')
  for j in range(32):
   v={n:rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   if j<8:v.update({n:rng.randrange(0,4) for n in p['parameters']})
   elif j>=8:v={n:rng.randrange(-3,4) for n in v}
   if j>=24:v={n:Fraction(k,3) for n,k in v.items()};counts['rational_identities']+=1
   a=run(parent['polynomial_source'],_pullback(p,v));b=run(p['polynomial_source'],v)
   need(a[parent['output']]==b[p['output']],'full numeric pullback');counts['complete_evaluations']+=1
   for l,r in p['comparisons']:need(a[l]-a[r]==b[l]-b[r],'retained residual numeric');counts['residual_evaluations']+=1
   if j<24:need(evaluate(p,v,signed=j>=8,root=root)==b[p['output']],'public evaluation')
  fixtures=[f for x in range(36) if (f:=outer_fixture(p,x)) is not None];counts['genuine_outer_fixtures']+=len(fixtures)
  # y=0 remains accepted by the domain API but not by a valid typed chronology.
  v={n:1 for n in p['parameters']+p['auxiliaries']};v.update(x=0,y=0,T=0)
  e=run(p['source'],v);need(e[p['interfaces']['height']]>0 and e['bridge_target']<=0,'y0 pretyping boundary')
  need(integer_pullback(p,v,root=root)['final_positive']==0,'signed pullback boundary explicit');counts['zero_output_boundary_cases']+=1
  evaluate(p,v,root=root)
  for key in p:
   bad=copy.deepcopy(p);del bad[key];reject(lambda bad=bad:checked(bad,root=root))
  for key in ['source','comparisons','auxiliaries','parent_pins','projection','degree']:
   bad=copy.deepcopy(p)
   if type(bad[key])is list:bad[key].clear()
   else:bad[key].clear()
   need(exact(build(variant,root=root),p),'returned defensive copy');counts['copies']+=1
  bad=copy.deepcopy(p);bad['polynomial_ledger']['M']=float(bad['polynomial_ledger']['M']);reject(lambda:checked(bad,root=root))
  for flag in [0,1,None]:reject(lambda flag=flag:evaluate(p,v,signed=flag,root=root))
  for value in [True,1.0,Fraction(1)]:
   bad=v.copy();bad['x']=value;reject(lambda bad=bad:evaluate(p,bad,signed=True,root=root))
  for name in ['x',p['auxiliaries'][0]]:
   bad=v.copy();bad[name]=-1;reject(lambda bad=bad:evaluate(p,bad,root=root))
  forms.append({'packet':p,'proof':proof,'outer_fixtures':fixtures})
 for variant in [None,0,True,'clock_bad']:reject(lambda variant=variant:build(variant,root=root))
 # Independent bounded integer chronology cancellation, including negative targets.
 for B in (3,4,5):
  from itertools import product
  for length in (1,2,3):
   for C in product(range(1,B),repeat=length):
    for N in product(range(1,B),repeat=length):
     for x in range(1,B):
      cw=sum(c*B**i for i,c in enumerate(C));nw=sum(n*B**i for i,n in enumerate(N))
      for target in range(-2,B+1):
       holds=B*nw+x==cw+B**length*target
       need(holds==(C[0]==x and all(C[i+1]==N[i] for i in range(length-1)) and N[-1]==target),'integer top-digit cancellation')
       counts['integer_chronology_cases']+=1
 # Every call reauthenticates changed sources, even after a successful build.
 with tempfile.TemporaryDirectory() as tmp:
  for name in PINS:Path(tmp,name).write_bytes(Path(root,name).read_bytes())
  build(root=tmp)
  for name in PINS:
   path=Path(tmp,name);raw=path.read_bytes();path.write_bytes(raw+b'\n')
   reject(lambda:build(root=tmp));path.write_bytes(raw);counts['warm_pin_checks']+=1
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':copy.deepcopy(PINS),'counts':dict(counts),'forms':forms,'scope':'Four literal complete sources plus general endpoint/height proof; finite outer tests do not materialize native Pell zeros.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();result=verify(args.root)
 if args.expect:need(exact(result,json.loads(args.expect.read_text())),'exact typed saved receipt')
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','counts':result['counts']},sort_keys=True))
if __name__=='__main__':main()
