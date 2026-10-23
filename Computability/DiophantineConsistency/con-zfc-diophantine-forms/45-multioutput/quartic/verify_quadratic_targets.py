#!/usr/bin/env python3
"""Independent standard-library audit of the quadratic multi-target certificate."""
import ast, collections, hashlib, itertools, json, pathlib, math
ROOT=pathlib.Path(__file__).resolve().parent
c=json.loads((ROOT/'QUADRATIC_TARGETS.json').read_text());src=(ROOT/c['source_file']).resolve();raw=src.read_bytes()
if hashlib.sha256(raw).hexdigest()!=c['source_sha256']:raise ValueError('source digest')
d=json.loads(raw);names=d['variables']+d['constants'];n=len(names);zero=(0,)*n
def add(a,b,sign=1):
 r=a.copy()
 for k,v in b.items():
  r[k]=r.get(k,0)+sign*v
  if not r[k]:del r[k]
 return r

def mul(a,b):
 r={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(i+j for i,j in zip(x,y));r[z]=r.get(z,0)+u*v
 return {k:v for k,v in r.items() if v}

def const(k):return {zero:k} if k else {}

def power(a,k):
 if not isinstance(k,int) or k<0:raise ValueError('invalid exponent')
 r=const(1)
 for _ in range(k):r=mul(r,a)
 return r

e={}
for i,x in enumerate(names):
 a=list(zero);a[i]=1;e[x]={tuple(a):1}
 if i<31:e[x]=add(e[x],const(1))

def get(x):return const(x) if isinstance(x,int) else e[x]
for out,op,x,y in d['source']:
 a,b=get(x),get(y)
 if op=='+':e[out]=add(a,b)
 elif op=='-':e[out]=add(a,b,-1)
 elif op=='*':e[out]=mul(a,b)
 else:raise ValueError('unrecognized operation')

residuals=[add(get(a),get(b),-1) for a,b in d['comparisons']]
portenv={}
for i,x in enumerate(d['constants'],31):
 a=list(zero);a[i]=1;portenv[x]={tuple(a):1}
def expr(t):
 if isinstance(t,ast.Constant) and type(t.value)==int:return const(t.value)
 if isinstance(t,ast.Name):return portenv[t.id]
 if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return mul(const(-1),expr(t.operand))
 if isinstance(t,ast.BinOp):
  if isinstance(t.op,ast.Pow):return power(expr(t.left),ast.literal_eval(t.right))
  a,b=expr(t.left),expr(t.right)
  if isinstance(t.op,ast.Add):return add(a,b)
  if isinstance(t.op,ast.Sub):return add(a,b,-1)
  if isinstance(t.op,ast.Mult):return mul(a,b)
 raise ValueError('invalid coefficient syntax')

b=json.loads((ROOT/'B2_CERTIFICATE.json').read_text());w=b['weights']
if w!=c['weights'] or len(w)!=31 or min(w)<=0 or max(w)!=799:raise ValueError('weights')
full=[]
for degree in range(3):
 for ids in itertools.combinations_with_replacement(range(31),degree):
  a=[0]*31
  for i in ids:a[i]+=1
  full.append((tuple(a),sum(w[i] for i in ids)))
if len(full)!=528 or len({v%1023 for a,v in full})!=528:raise ValueError('B2 collision')
spacing=2*max(w)+1
if c['target_spacing']!=spacing or c['target_maximum']!=22*spacing:raise ValueError('targets')
seen=set();total=0
for j,row in enumerate(c['rows'],1):
 index=row['original_row_one_based']-1
 if index in seen or not 0<=index<22:raise ValueError('row order')
 seen.add(index);expected=residuals[index];support={a[:31] for a in expected}
 if {tuple(t['alpha']) for t in row['terms']}!=support:raise ValueError('support')
 if row['target_exponent']!=j*spacing:raise ValueError('target position')
 for t in row['terms']:
  a=tuple(t['alpha']);code=sum(x*y for x,y in zip(a,w));factor=math.factorial(2-sum(a))*math.prod(math.factorial(x) for x in a)
  coef={zero[:31]+k[31:]:v for k,v in expected.items() if k[:31]==a}
  if expr(ast.parse(t['coefficient'],mode='eval').body)!=coef:raise ValueError('coefficient')
  if expr(ast.parse(t['weighted_coefficient'],mode='eval').body)!=mul(const(factor),coef):raise ValueError('weighted coefficient')
  if t['encoding_exponent']!=j*spacing-code or t['weight']!=code:raise ValueError('encoding exponent')
  for beta,v in full:
   e=j*spacing-code+v
   if e%spacing==0 and 1<=e//spacing<=22:
    if e//spacing!=j or beta!=a:raise ValueError('cross-target contamination')
  total+=1
if seen!=set(range(22)):raise ValueError('missing row')
last=c['rows'][-1];r=residuals[last['original_row_one_based']-1]
if r.get(zero,0)!=1 or any(k[:31]==zero[:31] and any(k[31:]) for k in r):raise ValueError('leading sign')
print(json.dumps({'status':'PASS','row_count':22,'shifted_row_terms':total,'full_degree_two_monomials':528,'maximum_weight':max(w),'target_spacing':spacing,'largest_target':22*spacing,'formal_leading_coefficient':2,'cross_target_pair_checks':total*528,'all_coefficients_independently_reconstructed':True},indent=2))
