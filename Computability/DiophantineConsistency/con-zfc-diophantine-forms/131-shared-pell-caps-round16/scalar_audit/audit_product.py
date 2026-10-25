#!/usr/bin/env python3
"""Independent exact audit, no import of producer or producer's checker/helpers."""
from pathlib import Path
from collections import Counter
import ast,copy,gzip,hashlib,json,sys
R=Path(__file__).resolve().parents[1];S=R/'scalar'
def need(x,msg):
 if not x:raise ValueError(msg)
def clean(x):return {m:c for m,c in x.items() if c}
def add(a,b,sg=1):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+sg*c
 return clean(z)
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));z[k]=z.get(k,0)+c*d
 return clean(z)
def power(a,n):
 z={():1}
 for _ in range(n):z=mul(z,a)
 return z
def expr(x,env):
 if isinstance(x,ast.Expression):return expr(x.body,env)
 if isinstance(x,ast.Name):return env[x.id]
 if isinstance(x,ast.Constant):return clean({():x.value})
 if isinstance(x,ast.UnaryOp) and isinstance(x.op,ast.USub):return {m:-c for m,c in expr(x.operand,env).items()}
 a=expr(x.left,env)
 if isinstance(x.op,ast.Pow):return power(a,x.right.value)
 b=expr(x.right,env)
 if isinstance(x.op,ast.Add):return add(a,b)
 if isinstance(x.op,ast.Sub):return add(a,b,-1)
 if isinstance(x.op,ast.Mult):return mul(a,b)
 raise ValueError('bad formula AST')
def formulas(short):return [
 ('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('W','12*w+4'),('X','q*W'),('Y','(2*v+1)*q**3'),('a','(X+1)*Y'),('H','4*a+3'),('Delta','(a+2)**2-1'),
 ('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J'),('index_modulus','4*q**4' if short else 'X*Y'),('k','R+1+h*index_modulus'),('eta','c-Y*k'),
 ('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('Budget','k**2*(q**2-Derr)-4*q**2*eta**2'),('ell','X*Y**2'),('Dt','1+ell*(ell+1)*k**2'),('D','Budget-4'),('P','Dt*(1+D*Dt*s**2)'),
 ('Amain','a+2'),('Dm','1+Delta*c**2'),('U','r*c**2*Amain*Dm'),('UP','U*P'),('Df','1+Delta*U**2*P'),('Q','Delta**2*U**2*P'),('delta','Q-1'),('b','c-R+4*UP*T'),('V','Df*b-c'),('Cy','Q*V**2-1'),
 ('K','X*(3*c-2*X)+2'),('S','s*r*H'),('zc','H*T+K'),('Ac','(zc**2+3*H**2)*(zc**3-19*H**3)'),('Z','S*n-Ac'),('output','delta*Z**2-S**2*P*Df*Cy')]
VARIABLES=['j','C','z','h','r','v','w','T','c','n','s'];PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def audit(d):
 nodes=d['nodes'];need(d['variables']==VARIABLES and d['variable_count']==11,'all eleven independent integers');need(d['domain']=='unrestricted integers','domain');need(d['coefficient_binding']=='coefficients/BINDING.json','ports binding')
 nm={**d['named_registers'],'output':d['output']};nm.update({n[1]:i for i,n in enumerate(nodes) if n[0] in ['variable','coefficient']})
 need([n[1] for n in nodes if n[0]=='variable']==VARIABLES,'variable leaf list');need([n[1] for n in nodes if n[0]=='coefficient']==PORTS,'coefficient leaf list')
 degrees=[]
 for i,n in enumerate(nodes):
  if n[0] in ['add','sub','mul']:
   need(len(n)==3 and all(type(k)==int and 0<=k<i for k in n[1:]),'DAG topology');degrees.append(sum(degrees[k] for k in n[1:]) if n[0]=='mul' else max(degrees[k] for k in n[1:]))
  else:need(n[0] in ['variable','coefficient','integer'] and len(n)==2,'leaf format');degrees.append(int(n[0]=='variable'))
 live=set();todo=[d['output']]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if nodes[i][0] in ['add','sub','mul']:todo+=nodes[i][1:]
 need(live==set(range(len(nodes))),'dead nodes')
 cnt=Counter(n[0] for n in nodes if n[0] in ['add','sub','mul']);want=110 if d['short_index'] else 109
 need(sum(cnt.values())==d['operations']==want and dict(cnt)==d['operation_counts'],'operation counts')
 covered=set();claims=[]
 for name,form in formulas(d['short_index']):
  tree=ast.parse(form,mode='eval');refs=sorted({n.id for n in ast.walk(tree) if isinstance(n,ast.Name)});env={n:{(n,):1} for n in refs};cuts={nm[n]:p for n,p in env.items()};memo=dict(cuts)
  def ev(i):
   if i in memo:return memo[i]
   covered.add(i);n=nodes[i]
   if n[0]=='integer':p=clean({():n[1]})
   else:
    need(n[0] in ['add','sub','mul'],'unbound actual input '+str(n));a,b=ev(n[1]),ev(n[2]);p=mul(a,b) if n[0]=='mul' else add(a,b,-1 if n[0]=='sub' else 1)
   memo[i]=p;return p
  need(ev(nm[name])==expr(tree,env),'literal formula '+name);claims.append(name)
 need(all(i in covered for i,n in enumerate(nodes) if n[0] in ['add','sub','mul']),'every arithmetic gate covered')
 # Weighted graded lexicographic leading monomial, with coefficient ports of degree zero.
 order=['h','T','j','w','v','s','r','c','C','z','n']+PORTS;lead=[]
 def key(e):return (sum(e[:11]),)+e
 for i,n in enumerate(nodes):
  if n[0] in ['variable','coefficient']:
   e=[0]*len(order);e[order.index(n[1])]=1;v=(tuple(e),1)
  elif n[0]=='integer':v=((0,)*len(order),n[1])
  else:
   a,b=lead[n[1]],lead[n[2]]
   if n[0]=='mul':v=(tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
   elif key(a[0])>key(b[0]):v=a
   elif key(a[0])<key(b[0]):v=(b[0],b[1]*(-1 if n[0]=='sub' else 1))
   else:v=(a[0],a[1]+b[1]*(-1 if n[0]=='sub' else 1))
  need(v[1]!=0,'leading cancellation at gate '+str(i));lead.append(v)
 ex,co=lead[d['output']];short=d['short_index'];wants={'h':42,'T':2,'j':588,'w':70 if short else 112,'v':112 if short else 154,'s':16,'r':12,'c':40,'beta':588}
 need(dict(zip(order,ex))=={x:wants.get(x,0) for x in order},'exact leading exponents')
 two,three=(946,658) if short else (988,700);need(co==2**two*3**three,'exact integer coefficient');deg=sum(ex[:11]);need(deg==d['exact_degree']==d['syntactic_degree_bound']==degrees[d['output']],'exact total degree')
 return dict(variables=11,operations=want,degree=deg,counts=dict(cnt),formula_checks=len(claims),covered_arithmetic_gates=len([i for i in covered if nodes[i][0] in ['add','sub','mul']]),leading_exponents=wants,leading_coefficient=f'2^{two}*3^{three}*beta^588')
def controls(d):
 rejected=[]
 for name in ['D','P','U','Df','Q','b','S','Ac','output']:
  x=copy.deepcopy(d);i=x['named_registers'][name];n=x['nodes'][i];n[0]='add' if n[0]=='mul' else 'mul'
  try:audit(x)
  except ValueError:rejected.append(name)
  else:raise ValueError('unrejected '+name)
 for name,value in [('domain','nonnegative integers'),('operations',999)]:
  x=copy.deepcopy(d);x[name]=value
  try:audit(x)
  except ValueError:rejected.append(name)
  else:raise ValueError('unrejected '+name)
 return rejected
# The exact congruence proof reduces to these finite residue classes, exhaustively checked.
residues=set();checks=0
for q in range(0,16,2):
 for k in range(16):
  for eta in range(16):
   for cf in [0]:
    for cc in [0]:
     budget=(k*k*(q*q-(cf-q)**2-(cc-q)**2)-4*q*q*eta*eta)%16
     need(budget==(-(q*k)**2)%16 and budget in (0,12),'guard parity')
     D=(budget-4)%16;need(D in (8,12) and D not in {a*a%16 for a in range(16)},'nonsquare');residues.add(budget);checks+=1
# Bind against authenticated incoming bytes, not only a mutable local manifest.
EXPECTED_SOURCE_DIGESTS={'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea', 'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af', 'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777', 'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722', 'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615', 'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}
binding=json.load(open(S/'coefficients/BINDING.json'));ports=[]
for name,meta in binding['payloads'].items():
 raw=gzip.decompress((S/'coefficients'/meta['file']).read_bytes())
 need(hashlib.sha256(raw).hexdigest()==EXPECTED_SOURCE_DIGESTS[name],'authentic source coefficient '+name);need(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'] and len(raw)==meta['raw_bytes'],'coefficient hash/length');v=int.from_bytes(raw,'little');need(v.bit_length()==meta['bits'],'coefficient bits');ports.append(dict(name=name,sha256=meta['raw_sha256'],bits=v.bit_length()))
 if name=='beta':need(v==2**1064921-1,'beta value')
 if name=='cone_A':need(v==2**1113,'coneA value')
 if name=='cone_B':need(v==2**666104,'coneB value')
results=[]
for deg in [966,882]:
 p=S/f'product11_degree{deg}.json';d=json.load(open(p));r=audit(d);r.update(file=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),rejected_mutations=controls(d));results.append(r)
out=dict(status='PASS',scope='Exact finite formula, degree, byte and residue audit; see SEMANTIC_REVIEW.md for unbounded proof.',equations=results,ports=ports,exhaustive_mod16_cases=checks,budget_residues=sorted(residues))
filename='INDEPENDENT_NORMAL.json' if __debug__ else 'INDEPENDENT_OPTIMIZED.json';Path(__file__).with_name(filename).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
