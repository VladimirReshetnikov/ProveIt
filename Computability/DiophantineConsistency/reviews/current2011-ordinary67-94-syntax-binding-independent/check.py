#!/usr/bin/env python3
"""Independent hash-consed arithmetic syntax comparison, without Lean."""
import ast,collections,gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary67-94-syntax-binding';G=D/'research/current2011-ordinary67-94-candidate/polynomial.json';L=D/'Lean/DiophantineConsistency/Carrier94Syntax.lean';C=D/'research/fourteen-nonzero-spheres/coefficients'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'check.py','cfd87109087e1786ff9b506230f5e5f998ad833d627c3a050c514c39dce1891d'),(P/'result.json','6df0d0b95ebc667a93b744a449d4e8de01685d83ead3f2992e5721b1cfe5151b'),(G,'d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb'),(L,'b68f54257ff1ebab090ed45e83d6c3719be51ccb0f7a7f03822e333bbb43ea8d')]:need(H(p)==h,'pin '+str(p))
graph=json.loads(G.read_text());need(graph['witnesses']==['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'] and graph['fixed_numerals']==['beta','K0','MC','MF'],'input order')
class Canon:
 def __init__(self):self.tab={};self.nodes=[]
 def node(self,k):
  if k not in self.tab:self.tab[k]=len(self.nodes);self.nodes.append(k)
  return self.tab[k]
 def number(self,n):return self.node(('n',n))
 def add(self,a,b,sign=1):
  weights=collections.Counter();constant=0
  for index,mult in ((a,1),(b,sign)):
   node=self.nodes[index]
   if node[0]=='n':constant+=mult*node[1]
   elif node[0]=='sum':
    constant+=mult*node[2]
    for key,count in node[1]:weights[key]+=mult*count
   else:weights[index]+=mult
  terms=tuple(sorted((k,v) for k,v in weights.items() if v))
  if not terms:return self.number(constant)
  if len(terms)==1 and terms[0][1]==1 and constant==0:return terms[0][0]
  return self.node(('sum',terms,constant))
 def mul(self,a,b):
  values=[]
  for index in (a,b):
   node=self.nodes[index];values.extend(node[1] if node[0]=='mul' else (index,))
  return self.node(('mul',tuple(sorted(values))))
 def operation(self,op,a,b):return self.mul(a,b) if op=='*' else self.add(a,b,1 if op=='+' else -1)
 def parse(self,expr,env):
  expr=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),expr)
  def go(x):
   if isinstance(x,ast.Name):need(x.id in env,'unknown name '+x.id);return env[x.id]
   if isinstance(x,ast.Constant) and type(x.value)==int:return self.number(x.value)
   if isinstance(x,ast.BinOp):
    if isinstance(x.op,ast.Pow):
     need(isinstance(x.right,ast.Constant) and x.right.value in (2,3),'unsupported exponent');base=go(x.left);out=base
     for _ in range(1,x.right.value):out=self.mul(out,base)
     return out
    op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(x.op));need(op is not None,'operator');return self.operation(op,go(x.left),go(x.right))
   raise RuntimeError('unsupported expression '+ast.dump(x))
  return go(ast.parse(expr.replace('^','**'),mode='eval').body)
def compare(source):
 c=Canon();g={x:c.node(('v',x)) for x in graph['witnesses']+graph['fixed_numerals']};edges={};counts=collections.Counter()
 for n,op,a,b in graph['source']:
  need(n not in g and op in ('+','-','*'),'bad gate')
  def val(x):
   if type(x)==int:return c.number(x)
   need(x in g,'non-topological');return g[x]
  g[n]=c.operation(op,val(a),val(b));edges[n]=(a,b);counts[op]+=1
 block=source.split('def expressionAt94 (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('/-- At the maintained current ports.',1)[0]
 chunks=[];output=[]
 for line in block.splitlines():
  if line.startswith('  let '):chunks.append([line.strip()])
  elif line.startswith('  P * Q'):output.append(line.strip())
  elif line.strip():
   if output:output.append(line.strip())
   else:need(bool(chunks),'orphan');chunks[-1].append(line.strip())
 env={f'port{i}':c.node(('v',v)) for i,v in enumerate(graph['fixed_numerals'])};seen=[]
 for chunk in chunks:
  match=re.fullmatch(r'let\s+(\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*)',' '.join(chunk));need(match is not None,'bad let');name,expr=match.groups();need(name not in seen,'duplicate let');seen.append(name);v=re.fullmatch(r'\.var\s+(\d+)',expr)
  if v:
   i=int(v.group(1));need(i<len(graph['witnesses']) and name==graph['witnesses'][i],'variable index');env[name]=c.node(('v',name))
  else:env[name]=c.parse(expr,env)
 need(seen[:14]==graph['witnesses'] and output,'variable prefix/output')
 cuts={'b':'qm','q':'q','C':'C','X':'X','Y':'Y','E':'E','k':'k','ell':'ell','c':'c','a':'a','H':'H','delta':'Delta','D':'main_root','rank':'R','tau':'tau','V':'V','P':'N0','Q':'N1','W':'Nt','U':'Na','Z':'Ns'}
 cut_equal={a:env[a]==g[b] for a,b in cuts.items()};equal=c.parse(' '.join(output),env)==g[graph['output']]
 used=set();leaves=set();stack=[graph['output']]
 while stack:
  n=stack.pop()
  if n in edges:
   if n not in used:used.add(n);stack.extend(edges[n])
  elif isinstance(n,str):leaves.add(n)
 need(len(used)==len(graph['source'])==67 and leaves==set(graph['witnesses']+graph['fixed_numerals']) and dict(counts)=={'*':37,'+':17,'-':13},'liveness/count')
 return equal,cut_equal,dict(counts)
source=L.read_text();equal,cuts,counts=compare(source);need(equal and all(cuts.values()),'canonical full-output/cuts mismatch')
for old,new in [('let X := w * q','let X := f * q'),('let Z := 1 + I ^ 2 - Aaux','let Z := 1 + I ^ 2 + Aaux')]:
 mutant=source.replace(old,new,1);need(mutant!=source,'mutation absent');match,_,_=compare(mutant);need(not match,'mutation passed '+old)
for n,m in graph['coefficient_binding']['ports'].items():
 p=C/m['file'];need(H(p)==m['gzip_sha256'],'compressed '+n);raw=gzip.decompress(p.read_bytes());need(hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'],'raw '+n)
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);need(q.returncode==0 and q.stdout==(P/'result.json').read_bytes(),'author audit rerun')
print(json.dumps({'status':'PASS_INDEPENDENT_SOURCE_DAG_AUDIT','operation_counts':counts,'live_rows':67,'checked_cuts':len(cuts),'witness_and_strong_sign_mutations':'rejected','source_and_graph_equal_mod_AC_and_signed_additive_normalization':True,'scope':'External source-to-graph identity only; no Lean build, object provenance, total-degree or PDF proof.'},indent=2,sort_keys=True))
