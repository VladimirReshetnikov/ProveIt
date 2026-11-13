#!/usr/bin/env python3
"""Independent AST-based parser of the pinned core fragments; no TeX semantics."""
import pathlib,hashlib,re,ast,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/current14-tex-syntax-structural-audit';T=D/'equation.tex';L=D/'Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(P/'check.py')=='088333294d671a6c47a161f501b7b3edf6afca0d458f0003761c3407b90a5769' and sha(P/'result.json')=='92b0326e9280e64b0431e3c6a3697c3bb4eba2fba598b4d29c715f910b338913'
assert sha(T)=='94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635' and sha(L)=='112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9'
t=T.read_text();l=L.read_text();greeks=['alpha','beta','eta','zeta','gamma','Delta','ell','mu','omega','tau'];mapped={x:('delta' if x=='Delta' else x) for x in greeks}
coords=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'];ports=['beta','K','mu','omega'];nodes=[];pool={}
def intern(x):
 if x not in pool:pool[x]=len(nodes);nodes.append(x)
 return pool[x]
initial={n:intern(('var',i)) for i,n in enumerate(coords)};initial.update({n:intern(('port',i)) for i,n in enumerate(ports)})
def expression(e,env):
 e=re.sub(r'Expr\.constant\s*\(p\s+([0-3])\)',lambda m:ports[int(m[1])],e)
 e=re.sub(r'\\([A-Za-z]+)',lambda m:mapped[m[1]],e).replace('[','(').replace(']',')').replace('{','(').replace('}',')')
 # Protect named identifiers, then split remaining one-letter products as TeX uses implicit multiplication.
 tokenpat=r'alpha|beta|eta|zeta|gamma|delta|ell|omega|tau|mu|rank|[A-Za-z]|[0-9]+|[-+*^()]'
 ts=re.findall(tokenpat,e);assert ''.join(ts)==''.join(e.split()),e
 def isend(x):return x==')' or x.isdigit() or x in env or x=='rank'
 def isstart(x):return x=='(' or x.isdigit() or x in env or x=='rank'
 out=[]
 for token in ts:
  if out and isend(out[-1]) and isstart(token):out.append('*')
  out.append('**' if token=='^' else token)
 node=ast.parse(''.join(out),mode='eval').body
 def visit(a):
  if isinstance(a,ast.Constant) and type(a.value)==int:return intern(('num',a.value))
  if isinstance(a,ast.Name):return env['R' if a.id=='rank' else a.id]
  if isinstance(a,ast.BinOp):
   if isinstance(a.op,ast.Pow):assert isinstance(a.right,ast.Constant) and type(a.right.value)==int;return intern(('pow',visit(a.left),a.right.value))
   op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(a.op)];return intern((op,visit(a.left),visit(a.right)))
  raise ValueError(ast.dump(a))
 return visit(node)
def compare(tex,lean):
 m=re.search(r'The only unknowns are\s*\\\[(.*?)\\\]',tex,re.S);assert m;domain=re.sub(r'\s+','',m.group(1));assert domain==r'J,F,\alpha,z,f,i,T,s,w,n,\eta,\zeta,y,\gamma\in\mathbbZ_{>0}.'
 m=re.search(r'All other symbols in the equation are polynomial abbreviations:.*?\\begin\{gathered\}(.*?)\\end\{gathered\}',tex,re.S);assert m;body=m.group(1).replace('\\\\',',').replace('\\quad',',').strip().rstrip('.')
 te=dict(initial);td={}
 for item in body.split(','):
  if not item.strip():continue
  name,rhs=item.split('=');name=name.strip().lstrip('\\');name=mapped.get(name,name);assert name not in te;td[name]=te[name]=expression(rhs,te)
 m=re.search(r'def expressionAt \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) :=(.*?)(?=/-- The current ports)',lean,re.S);assert m;body=m.group(1)
 variables=re.findall(r'let\s+(\w+)\s*:\s*Expr\s*\(Fin 14\)\s*:=\s*\.var\s+(\d+)',body);assert variables==[(n,str(i)) for i,n in enumerate(coords)]
 body=re.sub(r'  let \w+ : Expr \(Fin 14\) := \.var \d+\s*\n','\n',body);chunks=re.split(r'\n\s*let\s+',body);le=dict(initial);ld={};final=None
 for chunk in chunks[1:]:
  name,rhs=chunk.split(' := ',1)
  if name=='Z':rhs,final=rhs.split('\n  ',1)
  name={'rank':'R'}.get(name,name);assert name not in le;ld[name]=le[name]=expression(rhs,le)
 assert set(td)==set(ld) and all(td[n]==ld[n] for n in td)
 m=re.search(r'\\boxed\{([^{}]+)\}',tex);assert m;left,right=m.group(1).split('=');assert right.strip().removesuffix('.')=='0' and expression(left,te)==expression(final,le)
 return len(td)
assert compare(t,l)==22
mutations=[('tex',r'S=i\Delta c^2',r'S=i\Delta c^3'),('tex',r'PQUWZ-\Delta=0',r'PQUWZ+\Delta=0'),('tex',r'J,F,\alpha,z',r'F,J,\alpha,z'),('tex',r'\mu+q\omega',r'\omega+q\mu'),('lean','let J : Expr (Fin 14) := .var 0','let J : Expr (Fin 14) := .var 1'),('lean','let S := i * delta * c ^ 2','let S := i * delta * c ^ 3'),('tex','X=wq','X=w+q'),('lean','let q := b + 1','let q := b + 2')]
for which,a,b in mutations:
 assert a in (t if which=='tex' else l)
 try:compare(t.replace(a,b,1) if which=='tex' else t,l.replace(a,b,1) if which=='lean' else l)
 except (AssertionError,KeyError,ValueError,IndexError,SyntaxError):pass
 else:raise RuntimeError('mutation escaped '+a)
assert r'\rho=2^{47}' in t and compare(t.replace(r'\rho=2^{47}',r'\rho=2^{48}',1),l)==22
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'result.json').read_bytes()
print(json.dumps({'status':'PASS','declarations':22,'independent_mutations_rejected':len(mutations),'out_of_scope_coefficient_mutation_accepted':True,'scope':'External independent AST comparison of pinned 14-variable TeX core and Lean source; no PDF, coefficient recipes, degree or Lean parser semantics.'},indent=2))
