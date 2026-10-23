#!/usr/bin/env python3
"""Independent, standard-library-only symbolic replay and exhaustive isolation check.
No code from the source archive is imported or executed.  A finite coefficient
identity is checked in the polynomial ring Z[n_1,...,n_31,beta,K0,MC,MF].
"""
import ast,hashlib,itertools,json,math,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parent

def add(a,b,sign=1):
 c=dict(a)
 for m,v in b.items():
  c[m]=c.get(m,0)+sign*v
  if not c[m]:del c[m]
 return c

def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   t=tuple(x+y for x,y in zip(m,n));c[t]=c.get(t,0)+v*w
 return {m:v for m,v in c.items()if v}

def const(v,n):return {(0,)*n:v}if v else {}
def var(i,n):return {tuple(int(j==i)for j in range(n)):1}

def parse_coefficient(text,names):
 n=len(names)
 def rec(t):
  if isinstance(t,ast.Constant)and type(t.value)is int:return const(t.value,n)
  if isinstance(t,ast.Name):return var(names.index(t.id),n)
  if isinstance(t,ast.UnaryOp)and isinstance(t.op,ast.USub):return {m:-v for m,v in rec(t.operand).items()}
  if isinstance(t,ast.BinOp):
   a=rec(t.left)
   if isinstance(t.op,ast.Pow):
    assert isinstance(t.right,ast.Constant)and type(t.right.value)is int and 0<=t.right.value<=4
    b=const(1,n)
    for _ in range(t.right.value):b=mul(b,a)
    return b
   b=rec(t.right)
   if isinstance(t.op,ast.Add):return add(a,b)
   if isinstance(t.op,ast.Sub):return add(a,b,-1)
   if isinstance(t.op,ast.Mult):return mul(a,b)
  raise ValueError('Unrecognized coefficient syntax')
 return rec(ast.parse(text,mode='eval').body)

def verify(path):
 cert=json.loads(path.read_text());srcpath=ROOT/cert['source_file'];raw=srcpath.read_bytes();assert hashlib.sha256(raw).hexdigest()==cert['source_sha256'];src=json.loads(raw)
 assert cert['variables']==src['variables'];assert cert['ports']==src['constants'];nv=len(src['variables']);np=len(src['constants']);n=nv+np
 env={name:add(var(i,n),const(1,n))for i,name in enumerate(src['variables'])};env.update({name:var(nv+i,n)for i,name in enumerate(src['constants'])})
 def get(x):return const(x,n)if type(x)is int else env[x]
 for name,op,a,b in src['source']:
  assert name not in env
  env[name]= {'+':lambda:add(get(a),get(b)),'-':lambda:add(get(a),get(b),-1),'*':lambda:mul(get(a),get(b))}[op]()
 polys=[]
 for a,b in src['comparisons']:
  out={}
  for m,v in add(get(a),get(b),-1).items():
   alpha=m[:nv];assert sum(alpha)<=2;out.setdefault(alpha,{})[m[nv:]]=v
  polys.append(out)
 w=cert['weights'];padding=cert.get('padding_exponent',0);assert len(w)==nv and len(set(w+[padding]))==nv+1 and min(w+[padding])>=0
 W=max(w+[padding]);assert cert['maximum_weight']==W
 if 'normalization' in cert:
  norm=cert['normalization'];assert norm['normalized_positions']==[padding]+w;assert [x-norm['translation_subtracted']for x in norm['original_positions']]==[padding]+w
 assert cert.get('coefficient_signs',[1]*22)==[1]*22
 exp=[]
 for a in range(nv+1):
  for b in range(a,nv+1):
   alpha=[0]*nv
   if a:alpha[a-1]+=1
   if b:alpha[b-1]+=1
   exp.append((tuple(alpha),(2-sum(alpha))*padding+sum(x*y for x,y in zip(alpha,w))))
 assert len(exp)==528
 active=set();D={};rows=cert['rows'];assert len(rows)==22
 H=[r['target_exponent']for r in rows];assert len(set(H))==22;assert H==cert['target_exponents']
 for r in rows:
  terms={tuple(t['alpha']):parse_coefficient(t['coefficient'],src['constants'])for t in r['terms']}
  assert terms==polys[r['original_row_one_based']-1]
  for t in r['terms']:
   alpha=tuple(t['alpha']);active.add(alpha);s=(2-sum(alpha))*padding+sum(a*b for a,b in zip(alpha,w));assert s==t['weight'];factor=math.factorial(2-sum(alpha))*math.prod(math.factorial(a)for a in alpha);assert factor==t['multinomial_inverse_weight']
   weighted={a:factor*v for a,v in terms[alpha].items()};assert weighted==parse_coefficient(t['weighted_coefficient'],src['constants']);e=r['target_exponent']-s;assert e==t['encoding_exponent']and e>=0
   assert e not in D,('D collision',e);D[e]=weighted
 for alpha in active:
  s=(2-sum(alpha))*padding+sum(a*b for a,b in zip(alpha,w));assert [(b,t)for b,t in exp if t==s]==[(alpha,s)],('active monomial not isolated',alpha)
 checks=0;hits=0
 for r in rows:
  for t in r['terms']:
   for alpha,s in exp:
    checks+=1;hit=t['encoding_exponent']+s
    if hit in H:
     hits+=1;assert hit==r['target_exponent']and alpha==tuple(t['alpha']),('cross-target contamination',r['original_row_one_based'],hit)
 maxD=max(D);assert maxD==cert['Dmax'];assert cert['target_maximum']==max(H)
 assert D[maxD]==const(2,np);assert cert['Kcode']==maxD+2*W
 return {'certificate':path.name,'source_sha256':cert['source_sha256'],'source_rows':len(rows),'source_variables':nv,'weighted_source_terms':len(D),'active_monomials':len(active),'expansion_monomials':len(exp),'source_term_expansion_checks':checks,'intended_target_hits':hits,'maximum_weight':W,'padding_exponent':padding,'target_exponents':H,'coefficient_signs':cert.get('coefficient_signs',[1]*22),'normalization_checked':'normalization' in cert,'Dmax':maxD,'Kcode':cert['Kcode'],'leading_coefficient':2,'verified':True}
if __name__=='__main__':
 paths=[pathlib.Path(p).resolve()for p in sys.argv[1:]]or sorted(ROOT.glob('CERTIFICATE_*.json'))
 results=[verify(p)for p in paths]
 print(json.dumps(results,indent=2));(ROOT/'VERIFICATION.json').write_text(json.dumps(results,indent=2)+'\n')
