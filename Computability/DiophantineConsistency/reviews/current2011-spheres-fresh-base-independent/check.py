#!/usr/bin/env python3
"""Independent exact syntax DAG and fixed-port degree witness; no Lean."""
import ast,collections,gzip,hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-spheres-fresh-base';S=D/'research/fourteen-nonzero-spheres';PRE=D/'reviews/normalized106-fresh-base-model-independent';prime=1000000007
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'FreshCarrierSpheres.lean':'a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5','check02.py':'c39d7551394fb32a02f36017145f52ce8016072517f7398d12c6ba462dea035d','bind_graphs.py':'ad6eb9e2d99a17bd23baa0ea94e18c3e47ee40673472f930be3365a6f2b87452','binding-result.json':'d46e0bc55e41538da7414b56d20745a46588e5ab8220a1d4cd3cbe5801e3f3b1','attempt01/result.json':'3ae37b05c0e6c738a81e69e1bf2568903bb3d7795012ee6a34483c4fc7748e0f','attempt01/outer-observation.json':'9d5b5e3ff84333ba3ceb08b92126f113ed0393ffdd9142c139f573ca1a582018','attempt02/result.json':'67159c8c4665700e59c6745b705f42ecc459ca6a38f79bd95545c8e7115c31d9','attempt02/outer-observation.json':'60860352feb412c613a1e1387dbf92562f487d62f7063df886fc8d2337beeacb'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
source=(P/'FreshCarrierSpheres.lean').read_text();block=source.split('def frontAt (p : Fin 4 → ℤ)',1)[1].split('/-- The 14/71/80',1)[0]
# Hash-cons exact syntax nodes; flatten only commutative + and *, preserve minus ordering.
class C:
 def __init__(self):self.nodes=[];self.ids={}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.nodes);self.nodes.append(key)
  return self.ids[key]
 def combine(self,op,a,b):
  if op in '+*':
   q=[]
   for x in (a,b):q.extend(self.nodes[x][1] if self.nodes[x][0]==op else (x,))
   return self.node((op,tuple(sorted(q))))
  return self.node(('-',a,b))
 def parse(self,expr,env):
  expr=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),expr)
  def go(x):
   if isinstance(x,ast.Name):need(x.id in env,'unknown '+x.id);return env[x.id]
   if isinstance(x,ast.Constant) and type(x.value)==int:return self.node(('n',x.value))
   if isinstance(x,ast.BinOp):
    if isinstance(x.op,ast.Pow):
     need(isinstance(x.right,ast.Constant) and x.right.value in (2,3),'power'); z=go(x.left);result=z
     for _ in range(1,x.right.value):result=self.combine('*',result,z)
     return result
    op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(x.op));need(op is not None,'op');return self.combine(op,go(x.left),go(x.right))
   raise RuntimeError('AST '+str(x))
  return go(ast.parse(expr.replace('^','**'),mode='eval').body)
clauses=re.findall(r'\n  let (\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*?)(?=\n  let |\n  final )',block,re.S);need(len(clauses)>14,'front let parsing')
actual_final=' '.join(block.split('\n  final ',1)[1].split());need(actual_final=='P Q (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) W (f ^ 2 - delta * (i * c ^ 2) ^ 2)','exact front output')
results={}
for prof,gh in [(71,'937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2'),(72,'70d6bd4ab1f4d4a868a4718543502734d250fca6a38eb64a5b90dda8107b3280')]:
 gp=S/f'polynomial{prof}.json';need(H(gp)==gh,'graph pin');g=json.loads(gp.read_text()); rr={x[0]:x for x in g['source']};need(all(rr[n]==v for n,v in {'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']}.items()),'N1 cancellation shape');C0=C();env={f'port{i}':C0.node(('v',v)) for i,v in enumerate(g['fixed_numerals'])};seen=set()
 for name,expr in clauses:
  need(name not in seen,'duplicate let');seen.add(name);expr=' '.join(expr.split());match=re.fullmatch(r'\.var (\d+)',expr)
  if match:
   idx=int(match.group(1));need(idx<len(g['witnesses']) and g['witnesses'][idx]==name,'witness index');env[name]=C0.node(('v',name))
  else:env[name]=C0.parse(expr,env)
 need(all(x in seen for x in g['witnesses']),'witness coverage');env['U']=C0.parse('delta*(f^2-1)*(V^2-y^2)+y^2',env);env['S']=C0.parse('f^2-delta*(i*c^2)^2',env)
 m=re.search(r'def expressionAt'+str(prof)+r' \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) :=\s*frontAt p fun P Q U W S => ([^\n]+)',source);need(m is not None,'wrapper');sourceout=C0.parse(m.group(1),env)
 gv={n:C0.node(('v',n)) for n in g['witnesses']+g['fixed_numerals']};edges={};counts=collections.Counter();deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']});poly={n:[0,1] for n in g['witnesses']}
 for n,meta in g['coefficient_binding']['ports'].items():
  z=(S/'coefficients'/meta['file']).read_bytes();need(hashlib.sha256(z).hexdigest()==meta['gzip_sha256'],'gzip '+n);raw=gzip.decompress(z);need(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'] and len(raw)==meta['raw_bytes'],'port '+n);poly[n]=[int.from_bytes(raw,'big')%prime]
 def univ(x,y,op):
  z=[0]*(len(x)+len(y)-1 if op=='*' else max(len(x),len(y)))
  if op=='*':
   for i,a in enumerate(x):
    for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%prime
  else:
   for i,a in enumerate(x):z[i]=(z[i]+a)%prime
   for i,b in enumerate(y):z[i]=(z[i]+(1 if op=='+' else -1)*b)%prime
  while len(z)>1 and not z[-1]:z.pop()
  return z
 for n,op,x,y in g['source']:
  need(n not in gv and op in '+-*' and all(isinstance(q,int) or q in gv for q in (x,y)),'graph topology');a=gv[x] if isinstance(x,str) else C0.node(('n',x));b=gv[y] if isinstance(y,str) else C0.node(('n',y));gv[n]=C0.combine(op,a,b);edges[n]=(x,y);counts[op]+=1
  dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0;deg[n]=dx+dy if op=='*' else max(dx,dy)
  if n=='N1':
   need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'degree N1 assumptions');deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c']);need(deg[n]==18,'N1 cancellation bound')
  poly[n]=univ(poly[x] if isinstance(x,str) else [x%prime],poly[y] if isinstance(y,str) else [y%prime],op)
 need(sourceout==gv[g['output']],'full DAG modulo AC')
 todo=[g['output']];used=set();leaves=set()
 while todo:
  n=todo.pop()
  if n in edges:
   if n not in used:used.add(n);todo.extend(edges[n])
  elif isinstance(n,str):leaves.add(n)
 need(len(used)==len(g['source'])==prof and leaves==set(g['witnesses']+g['fixed_numerals']) and dict(counts)==g['operation_counts'],'liveness and count')
 expected={71:(80,397288807),72:(68,830588191)}[prof];ray=poly[g['output']];need((deg[g['output']],len(ray)-1,ray[-1])==(expected[0],expected[0],expected[1]),'independent degree')
 results[str(prof)]={'rows':len(used),'operation_counts':dict(counts),'degree_upper':deg[g['output']],'ray_leading_coefficient_mod_1000000007':ray[-1],'full_output_equal_mod_AC':True}
# Receipts and the directly selected fresh model object.
r=json.loads((P/'attempt02/result.json').read_text());t=json.loads((P/'attempt02/outer-observation.json').read_text());f=json.loads((P/'attempt01/result.json').read_text());ft=json.loads((P/'attempt01/outer-observation.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==233,'result');need(t['session_id']==31123 and t['observed_outer_exit']==0 and f['status']=='FAILED' and f['exit']==0 and ft['session_id']==95954 and ft['observed_outer_exit']==1,'outer exits');need('warning:' in (P/'attempt01/compile.log').read_text() and H(P/'attempt01/compile.log')==f['log_sha256'],'failed warning log')
for n,x in r['guards_after'].items():
 q=Path(x['path'] if x is not None and 'path' in x else n.rsplit(':',1)[-1])
 if x is None:need(not os.path.lexists(q),'unexpected '+n)
 else:need(q.is_file() and str(q.resolve())==x['realpath'] and H(q)==x['sha256'],'guard '+n)
need(any(n.endswith('/FreshModel106.olean') and x and x['sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942' for n,x in r['guards_after'].items()),'fresh model provider')
l=(P/'attempt02/compile.log').read_text();need(H(P/'attempt02/compile.log')==r['log_sha256']=='0add61f4cb95515a1541d4f206f7ea00357f33e67a5300e9e9085203a6af790e' and l.count('depends on axioms:')==4 and l.count('Classical.choice')==4 and not any(x in l for x in ('sorryAx','warning:','error:')),'success log');reports=re.findall(r"'DiophantineConsistency\.FreshCarrierSpheres\.(\w+)' depends on axioms: \[([^]]*)\]",l,re.S);need({n:{x.strip() for x in val.split(',')} for n,val in reports}=={n:{'propext','Classical.choice','Quot.sound'} for n in ('sameZero71','sameZero72','standard_equivalence71','standard_equivalence72')},'exact axiom reports');need(H(Path('/tmp/current2011-spheres-fresh-base-priority-check02/FreshCarrierSpheres.olean'))==r['object_sha256']=='37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020','object')
for script,output in [(P/'bind_graphs.py',P/'binding-result.json'),(PRE/'check.py',PRE/'result.json')]:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(script)],capture_output=True);need(q.returncode==0 and q.stdout==output.read_bytes(),'prior audit '+str(script))
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','graphs':results,'prime':prime,'prior_model_audit_exit':0,'direct_and_nested_provider_slots':233,'outer_failure_session':95954,'success_session':31123,'scope':'External exact graph matching modulo AC and fixed-byte degree; source model/iPRA theorems; no Lean replay, PDF, or new transitive ancestry.'},sort_keys=True,indent=2))
