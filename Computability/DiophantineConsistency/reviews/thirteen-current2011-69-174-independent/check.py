#!/usr/bin/env python3
"""Independent canonical source-DAG and fixed-byte degree review; no Lean."""
import ast,collections,gzip,hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/thirteen-current2011-69-174';S=D/'research/thirteen-unit-sphere96';prime=1000000007
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'polynomial69.json','8667df5fe2f33c14a4280972336611218ebfb68883347bbfbb9215e5ab72a517'),(P/'build.py','3506aa65b54acdd8c502f150c8ee325134a8b3bc7f000076ec5f3ca3930b3bbe'),(P/'check.py','e4aaa2cd7aabcc54b3558c6948f9518f112ae5d2c4332c9dc8bea113e6b2ec26'),(P/'result.json','0ba9a076953cdaab688dae2c41a83a72c2e26098f66b211c414968c1fbedef53'),(S/'polynomial.json','48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1')]:need(H(p)==h,'pin '+str(p))
carrierpath=D/'research/thirteen-current2011-carrier-split-draft/src/DiophantineConsistency/ModelThirteenCarrierCore.lean';need(H(carrierpath)=='394d7b25748bb93ac285f6bac763d948364ce12277a6ccf999dc6915f3864dc9','checked core source');carrier=carrierpath.read_text();block=carrier.split('def front13 (p : Fin 4 → ℤ)',1)[1].split('/-- The 13/69/174',1)[0];clauses=re.findall(r'\n  let (\w+)(?:\s*:\s*Expr\s*\(Fin\s+13\))?\s*:=\s*(.*?)(?=\n  let |\n  final )',block,re.S);final=' '.join(block.split('\n  final ',1)[1].split());need(final=='(tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) (delta * (b * i * c ^ 2)) f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)','front output')
class C:
 def __init__(self):self.nodes=[];self.ids={}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.nodes);self.nodes.append(key)
  return self.ids[key]
 def number(self,n):return self.node(('n',n))
 def plus(self,a,b,sign=1):
  terms=collections.Counter();const=0
  for x,mult in ((a,1),(b,sign)):
   v=self.nodes[x]
   if v[0]=='n':const+=mult*v[1]
   elif v[0]=='sum':
    const+=mult*v[2]
    for term,count in v[1]:terms[term]+=mult*count
   else:terms[x]+=mult
  z=tuple(sorted((key,val) for key,val in terms.items() if val));
  if not z:return self.number(const)
  if len(z)==1 and z[0][1]==1 and const==0:return z[0][0]
  return self.node(('sum',z,const))
 def mul(self,a,b):
  terms=[]
  for x in (a,b):terms.extend(self.nodes[x][1] if self.nodes[x][0]=='mul' else (x,))
  return self.node(('mul',tuple(sorted(terms))))
 def op(self,op,a,b):return self.mul(a,b) if op=='*' else self.plus(a,b,1 if op=='+' else -1)
 def parse(self,expr,env):
  expr=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),expr)
  def go(x):
   if isinstance(x,ast.Name):need(x.id in env,'unknown name '+x.id);return env[x.id]
   if isinstance(x,ast.Constant) and type(x.value)==int:return self.number(x.value)
   if isinstance(x,ast.BinOp):
    if isinstance(x.op,ast.Pow):
     need(isinstance(x.right,ast.Constant) and x.right.value in (2,3),'power');z=go(x.left);out=z
     for _ in range(1,x.right.value):out=self.mul(out,z)
     return out
    op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(x.op));need(op is not None,'op');return self.op(op,go(x.left),go(x.right))
   raise RuntimeError('unsupported AST')
  return go(ast.parse(expr.replace('^','**'),mode='eval').body)
base=json.loads((S/'polynomial.json').read_text());ports=base['coefficient_binding']['ports'];fixed={}
for n,m in ports.items():
 p=S/'coefficients'/m['file'];need(H(p)==m['gzip_sha256'],'compressed '+n);raw=gzip.decompress(p.read_bytes());need(hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'],'payload '+n);need(int.from_bytes(raw,'big').bit_length()==m['bits'],'bit length '+n);fixed[n]=int.from_bytes(raw,'big')%prime

def univ(a,b,op):
 out=[0]*(len(a)+len(b)-1 if op=='*' else max(len(a),len(b)))
 if op=='*':
  for i,x in enumerate(a):
   for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
 else:
  for i,x in enumerate(a):out[i]=(out[i]+x)%prime
  for i,y in enumerate(b):out[i]=(out[i]+(1 if op=='+' else -1)*y)%prime
 while len(out)>1 and not out[-1]:out.pop()
 return out
g=json.loads((P/'polynomial69.json').read_text());need(g['coefficient_binding']['path']=='../thirteen-unit-sphere96/coefficients/','port path');need(g['coefficient_binding']['ports']==ports,'port metadata');need(g['witnesses']==['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma'] and g['fixed_numerals']==['beta','K0','MC','MF'],'input order');c=C();env={f'port{i}':c.node(('v',x)) for i,x in enumerate(g['fixed_numerals'])};names=set()
for n,e in clauses:
 need(n not in names,'duplicate let');names.add(n);e=' '.join(e.split());m=re.fullmatch(r'\.var (\d+)',e)
 if m:
  j=int(m.group(1));need(j<len(g['witnesses']) and g['witnesses'][j]==n,'witness '+n);env[n]=c.node(('v',n))
 else:env[n]=c.parse(e,env)
for n,e in {'P':'tau^2-ell*(ell+k)','Q':'D^2-delta*c^2','S':'delta*(b*i*c^2)','gap':'V^2-y^2'}.items():env[n]=c.parse(e,env)
m=re.search(r'def expressionAt69 \(p : Fin 4 → ℤ\) : Expr \(Fin 13\) :=\s*front13 p fun P Q S f delta gap y _ =>\s*([^\n]+)',carrier);need(m is not None,'source wrapper');wrapper=m.group(1);sourceout=c.parse(wrapper,env)
gv={n:c.node(('v',n)) for n in g['witnesses']+g['fixed_numerals']};edges={};counts=collections.Counter();deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']});polys={n:[0,1] for n in g['witnesses']};polys.update({n:[fixed[n]] for n in g['fixed_numerals']});rows={r[0]:r for r in g['source']};shape={'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']};need(all(rows[k]==v for k,v in shape.items()),'main norm shape')
for n,op,x,y in g['source']:
 need(n not in gv and op in '+-*' and all(type(z)==int or z in gv for z in (x,y)),'topology');gv[n]=c.op(op,gv[x] if type(x)==str else c.number(x),gv[y] if type(y)==str else c.number(y));edges[n]=(x,y);counts[op]+=1
 dx=deg[x] if type(x)==str else 0;dy=deg[y] if type(y)==str else 0;deg[n]=dx+dy if op=='*' else max(dx,dy)
 if n=='N1':
  need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'N1 inputs');deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
 polys[n]=univ(polys[x] if type(x)==str else [x%prime],polys[y] if type(y)==str else [y%prime],op)
todo=[g['output']];seen=set();leaves=set()
while todo:
 n=todo.pop()
 if n in edges:
  if n not in seen:seen.add(n);todo.extend(edges[n])
 elif isinstance(n,str):leaves.add(n)
need(len(seen)==len(g['source'])==69 and leaves==set(g['witnesses']+g['fixed_numerals']) and dict(counts)==g['operation_counts'],'live graph');need(sourceout==gv[g['output']],'full syntax equality');wrong=c.parse(wrapper.replace('y ^ 2','y ^ 2 + 1',1),env);need(wrong!=gv[g['output']],'sign mutation');ray=polys[g['output']];need((deg[g['output']],len(ray)-1,ray[-1])==(174,174,737305404),'degree')
print(json.dumps({'status':'PASS','operations':dict(counts),'degree':174,'leading_ray_mod_prime':ray[-1],'prime':prime,'source_DAG_equal':True,'scope':'Source/graph and fixed-byte exact degree; external computation, no Lean file/degree theorem.'},indent=2,sort_keys=True))
