#!/usr/bin/env python3
"""Independent exact polynomial-ring reconstruction and full finite replay.
No imported generator, optimizer, upstream code, SymPy, or sampled witnesses.
"""
import ast,hashlib,itertools,json,math,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parent
PIN='ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48'
def scalar(x,n):return {(0,)*n:x} if x else {}
def variable(j,n):return {tuple(int(i==j) for i in range(n)):1}
def sum_poly(a,b,s=1):
 d=a.copy()
 for e,c in b.items():d[e]=d.get(e,0)+s*c
 return {e:c for e,c in d.items() if c}
def product(a,b):
 d={}
 for e,c in a.items():
  for f,k in b.items():
   z=tuple(x+y for x,y in zip(e,f));d[z]=d.get(z,0)+c*k
 return {e:c for e,c in d.items() if c}
def expression(text,names):
 n=len(names)
 def visit(node):
  if isinstance(node,ast.Constant) and type(node.value) is int:return scalar(node.value,n)
  if isinstance(node,ast.Name):return variable(names.index(node.id),n)
  if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return {e:-c for e,c in visit(node.operand).items()}
  assert isinstance(node,ast.BinOp)
  a=visit(node.left)
  if isinstance(node.op,ast.Pow):
   assert isinstance(node.right,ast.Constant) and type(node.right.value)is int and 0<=node.right.value<=8
   v=scalar(1,n)
   for _ in range(node.right.value):v=product(v,a)
   return v
  b=visit(node.right)
  if isinstance(node.op,ast.Add):return sum_poly(a,b)
  if isinstance(node.op,ast.Sub):return sum_poly(a,b,-1)
  if isinstance(node.op,ast.Mult):return product(a,b)
  raise AssertionError('Unrecognized operator')
 return visit(ast.parse(text,mode='eval').body)
def check(path):
 cert=json.loads(path.read_text());raw=(ROOT/cert['source_file']).read_bytes();assert hashlib.sha256(raw).hexdigest()==PIN==cert['source_sha256'];source=json.loads(raw)
 assert hashlib.sha256((ROOT/cert['source_variant_file']).read_bytes()).hexdigest()==cert['source_variant_sha256']
 nv=len(source['variables']);np=len(source['constants']);n=nv+np;assert nv==31 and np==4
 assert cert['variables']==source['variables'] and cert['ports']==source['constants']
 # Explicitly reconstruct the selective shifts from the original gate circuit.
 shifted=set(cert['shifted_coordinates']);assert shifted=={'F','alpha','z','h','i','j','s','w','eta','zeta','gamma','g'}
 env={name:sum_poly(variable(j,n),scalar(int(name in shifted),n)) for j,name in enumerate(source['variables'])}
 env.update({name:variable(nv+j,n) for j,name in enumerate(source['constants'])})
 for name in source['variables']:assert expression(cert['coordinate_map'][name],source['variables']+source['constants'])==env[name]
 def get(x):return scalar(x,n) if type(x)is int else env[x]
 for name,op,a,b in source['source']:
  assert name not in env
  env[name]=product(get(a),get(b)) if op=='*' else sum_poly(get(a),get(b),1 if op=='+' else -1)
 exact=[]
 for a,b in source['comparisons']:
  p={}
  for exponent,value in sum_poly(get(a),get(b),-1).items():
   alpha=exponent[:nv];assert sum(alpha)<=2;p.setdefault(alpha,{})[exponent[nv:]]=value
  exact.append(p)
 c=cert['padding_exponent'];w=cert['weights'];positions=[c]+w;assert len(w)==nv and len(set(positions))==32 and min(positions)==0
 W=max(positions);assert cert['maximum_weight']==W
 expansion=[]
 for a in range(32):
  for b in range(a,32):
   alpha=[0]*nv
   if a:alpha[a-1]+=1
   if b:alpha[b-1]+=1
   expansion.append((tuple(alpha),positions[a]+positions[b]))
 assert len(expansion)==528
 rows=cert['rows'];assert len(rows)==22 and sorted(r['original_row_one_based'] for r in rows)==list(range(1,23))
 H=cert['target_exponents'];assert H==[r['target_exponent'] for r in rows] and len(set(H))==22 and min(H)>=0
 signs=cert['coefficient_signs'];assert len(signs)==22 and set(signs)<={-1,1}
 # A portable nonnegative polynomial majorant in absolute port values.
 # Coefficientwise maxima dominate every individual weighted coefficient.
 envelope={};active=set();D={};Drow={};checks=hits=0
 for r in rows:
  j=r['original_row_one_based']-1;s=signs[j]
  terms={tuple(t['alpha']):expression(t['coefficient'],source['constants']) for t in r['terms']}
  assert terms=={a:{e:s*v for e,v in co.items()} for a,co in exact[j].items()}
  assert len(terms)==len(r['terms'])
  flattened={a+e:v for a,co in terms.items() for e,v in co.items()}
  assert expression(r['polynomial'],source['variables']+source['constants'])==flattened
  for t in r['terms']:
   a=tuple(t['alpha']);active.add(a);mult=math.factorial(2-sum(a))*math.prod(math.factorial(x) for x in a);assert mult==t['multinomial_inverse_weight']
   weighted={e:mult*v for e,v in terms[a].items()};assert expression(t['weighted_coefficient'],source['constants'])==weighted
   for e,v in weighted.items():envelope[e]=max(envelope.get(e,0),abs(v))
   m=(2-sum(a))*c+sum(x*y for x,y in zip(a,w));assert m==t['weight'];e=r['target_exponent']-m;assert e==t['encoding_exponent'] and e>=0 and e not in D;D[e]=weighted;Drow[e]=j+1
   for b,z in expansion:
    checks+=1
    if e+z in H:
     hits+=1;assert e+z==r['target_exponent'] and a==b
 for a in active:
  m=(2-sum(a))*c+sum(x*y for x,y in zip(a,w));assert [b for b,z in expansion if z==m]==[a]
 assert len(D)==109==cert['source_record_count'] and len(active)==62==cert['active_monomial_count']
 dmax=max(D);lead=cert['leading_encoded_coefficient'];assert type(lead)is int and lead>0 and D[dmax]==scalar(lead,np)
 assert cert['leading_row_one_based']==Drow[dmax]
 assert cert['Dmax']==dmax and cert['Kcode']==dmax+2*W and cert['target_maximum']==max(H)<=cert['Kcode']
 assert cert['sparse_padding_headroom']==cert['Kcode']-max(H)>=2
 # These two identities ensure a positive-weight digit at every nonnegative zero.
 assert exact[9]=={e[:nv]:{e[nv:]:v} for e,v in expression('Delta-a**2-4*a-3',source['variables']+source['constants']).items()}
 assert exact[11]=={e[:nv]:{e[nv:]:v} for e,v in expression('D**2-C2*Delta-1',source['variables']+source['constants']).items()}
 return dict(certificate=path.name,verified=True,source_sha256=PIN,source_variables=31,source_rows=22,source_records=len(D),active_monomials=len(active),expansion_monomials=len(expansion),source_term_expansion_checks=checks,intended_target_hits=hits,maximum_weight=W,padding_exponent=c,Dmax=dmax,Kcode=cert['Kcode'],target_maximum=max(H),leading_encoded_coefficient=lead,coefficient_signs=signs,absolute_coefficient_envelope=[{'port_exponents':list(e),'coefficient':v} for e,v in sorted(envelope.items())],positive_weight_witness_lemma='Delta >= 3 and D >= 1 at every nonnegative source zero; their positions are distinct')
if __name__=='__main__':
 paths=[pathlib.Path(p).resolve() for p in sys.argv[1:]] or sorted(ROOT.glob('CERTIFICATE_*.json'))
 results=[check(p) for p in paths];out=dict(verifier='independent standard-library exact symbolic and exhaustive positional replay',all_verified=bool(results) and all(x['verified'] for x in results),certificates=results)
 (ROOT/'VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
