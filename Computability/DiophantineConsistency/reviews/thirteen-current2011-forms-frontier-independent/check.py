#!/usr/bin/env python3
"""Independent 13-variable literal syntax, fixed-byte degree, and receipt review."""
import ast,collections,gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/thirteen-current2011-forms-frontier';L=D/'Lean/DiophantineConsistency';S=D/'research/thirteen-unit-sphere96';prime=1000000007
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'polynomial70.json','4bbd5df7cdbd5e62ece28816f87cfa76b062b50105fcbee146a430d8b2a931a3'),(P/'polynomial71.json','f649581e711570553355f48443b1fa3757a03ba57beeb7ec2a63c08b35bfb55a'),(P/'check.py','bfa2efc9493b0e524ad1dc4b013fb1a0a20409592604dcf4dc8a678b838b0ef6'),(P/'result.json','026ff7c72aa3fa3f41d3fea8c12f72465f69d4068ee02188f27f40924c4cb204'),(L/'ModelThirteenForms.lean','98d9dcc48895ffe026c029b2496a61a35b66bca2f7b2fd1b31b8acf43acbfb6f'),(L/'ModelThirteenCarrier.lean','57f3cf755891aa921e9d97877af373e9194c6aa709a259c47678e4a370fd0185'),(S/'polynomial.json','48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1')]:need(H(p)==h,'pin '+str(p))
forms=(L/'ModelThirteenForms.lean').read_text();carrier=(L/'ModelThirteenCarrier.lean').read_text();block=carrier.split('def front13 (p : Fin 4 → ℤ)',1)[1].split('/-- The 13/69/174',1)[0];clauses=re.findall(r'\n  let (\w+)(?:\s*:\s*Expr\s*\(Fin\s+13\))?\s*:=\s*(.*?)(?=\n  let |\n  final )',block,re.S);final=' '.join(block.split('\n  final ',1)[1].split());need(final=='(tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) (delta * (b * i * c ^ 2)) f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)','front output')
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
 p=S/'coefficients'/m['file'];need(H(p)==m['gzip_sha256'],'compressed '+n);raw=gzip.decompress(p.read_bytes());need(hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'],'payload '+n);fixed[n]=int.from_bytes(raw,'big')%prime

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
results={}
for profile,expected in [(70,(140,171890737)),(71,(128,39067118))]:
 g=json.loads((P/f'polynomial{profile}.json').read_text());need(g['coefficient_binding']['ports']==ports,'current fixed port metadata');need(g['witnesses']==['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma'] and g['fixed_numerals']==['beta','K0','MC','MF'],'input order');c=C();env={f'port{i}':c.node(('v',x)) for i,x in enumerate(g['fixed_numerals'])};names=set()
 for n,e in clauses:
  need(n not in names,'duplicate let');names.add(n);e=' '.join(e.split());m=re.fullmatch(r'\.var (\d+)',e)
  if m:
   j=int(m.group(1));need(j<len(g['witnesses']) and g['witnesses'][j]==n,'witness '+n);env[n]=c.node(('v',n))
  else:env[n]=c.parse(e,env)
 for n,e in {'P':'tau^2-ell*(ell+k)','Q':'D^2-delta*c^2','gap':'V^2-y^2','t':'b*i*c^2'}.items():env[n]=c.parse(e,env)
 m=re.search(r'def expressionAt'+str(profile)+r' \(p : Fin 4 → ℤ\) : Expr \(Fin 13\) :=\s*front13 p fun P Q _ f delta gap y t =>\s*([^\n]+)',forms);need(m is not None,'wrapper');wrapper=m.group(1);need('delta * (f ^ 2 - 1)' in wrapper,'expected distribution');env['localTheta']=c.node(('cut','delta*(f^2-1)'));sourceout=c.parse(wrapper.replace('delta * (f ^ 2 - 1)','localTheta'),env)
 gv={n:c.node(('v',n)) for n in g['witnesses']+g['fixed_numerals']};edges={};counts=collections.Counter();deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']});polys={n:[0,1] for n in g['witnesses']};polys.update({n:[fixed[n]] for n in g['fixed_numerals']});rows={r[0]:r for r in g['source']};shape={'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']};need(all(rows[k]==v for k,v in shape.items()),'main norm shape')
 for n,op,x,y in g['source']:
  need(n not in gv and op in '+-*' and all(type(z)==int or z in gv for z in (x,y)),'topology');gv[n]=c.op(op,gv[x] if type(x)==str else c.number(x),gv[y] if type(y)==str else c.number(y));edges[n]=(x,y);counts[op]+=1
  dx=deg[x] if type(x)==str else 0;dy=deg[y] if type(y)==str else 0;deg[n]=dx+dy if op=='*' else max(dx,dy)
  if n=='N1':
   need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'N1 inputs');deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
  polys[n]=univ(polys[x] if type(x)==str else [x%prime],polys[y] if type(y)==str else [y%prime],op)
  if n=='Theta':need(rows['Theta']==['Theta','-','scaled_f2','Delta'] and rows['scaled_f2']==['scaled_f2','*','Delta','f2'] and gv['Delta']==env['delta'] and gv['f2']==c.parse('f^2',env),'one distributive cut');gv[n]=env['localTheta']
 todo=[g['output']];seen=set();leaves=set()
 while todo:
  n=todo.pop()
  if n in edges:
   if n not in seen:seen.add(n);todo.extend(edges[n])
  elif isinstance(n,str):leaves.add(n)
 need(len(seen)==len(g['source'])==profile and leaves==set(g['witnesses']+g['fixed_numerals']) and dict(counts)==g['operation_counts'],'live graph');need(sourceout==gv[g['output']],'full syntax equality');wrong=c.parse(wrapper.replace('delta * (f ^ 2 - 1)','delta * (f ^ 2 + 1)'),env);need(wrong!=gv[g['output']],'sign mutation not rejected');ray=polys[g['output']];need((deg[g['output']],len(ray)-1,ray[-1])==(expected[0],expected[0],expected[1]),'degree');results[str(profile)]={'operations':dict(counts),'degree':expected[0],'leading_ray_mod_prime':ray[-1],'full_DAG_equal':True}
# Existing recorded endpoint provenance; current historical provider is not replayed here.
receipt=D/'research/thirteen-model-lowdegree-suffix/replay-receipt.json';terminal=D/'research/thirteen-model-lowdegree-suffix/terminal-observation.json';progress=D/'research/thirteen-model-endpoint-successor/progress.json';review=D/'reviews/thirteen-model-lowdegree-suffix-independent-audit/CHECK.json'
for p,h in [(receipt,'2ca8a5e4d7f417b5c6e3a0f00bba71f529e98af2497e089f024a2743e52c5f2c'),(terminal,'f76b0162f8dd779ed9b0c6dcb9f59574584688a89533255e023777f2cb00086a'),(progress,'d4cf3098987576422ea21b81b7c90c2151fa1d8cdf969cdc0271524490af12ac'),(review,'01b4f92fd866c2d34b1954527664c94df22f118dd3d5fee010bb71b7853daa83')]:need(H(p)==h,'historical receipt '+str(p))
r=json.loads(receipt.read_text());t=json.loads(terminal.read_text());need(r['status']=='PASS_PAIRED_THIRTEEN_LOWDEGREE_SUFFIX' and t['session']==56787 and t['actual_exit_code']==0 and t['receipt_sha256']==H(receipt),'historical terminal');pairs=[x for x in r['rows'] if x.get('module')=='ModelThirteenForms'];need(len(pairs)==2 and {x['side'] for x in pairs}=={'author','peer'} and all(x['exit']==0 and x['source_sha256']==H(L/'ModelThirteenForms.lean') and x['object_sha256']=='2d881b56c3c7677f8488658b406f80b5da01cb8212cf4ffa103bffb4521a31e4' for x in pairs),'historical forms records')
carrierrows=[x for x in json.loads(progress.read_text()) if x.get('module')=='DiophantineConsistency.ModelThirteenCarrier'];need(len(carrierrows)==2 and {x['side'] for x in carrierrows}=={'author','peer'} and all(x['exit']==0 and x['source_sha256']==H(L/'ModelThirteenCarrier.lean') and x['object_sha256']=='b125021553fc8dde21920f4bed5be42fbd9919cbab8c79189f1971f1765dedf6' for x in carrierrows),'historical carrier records')
for side in ('author','peer'):
 path=f'/tmp/ipra-thirteen-lowdegree-pair-01/{side}/lib/DiophantineConsistency/ModelThirteenCarrier.olean';need(r['direct_guards'][path]['sha256']=='b125021553fc8dde21920f4bed5be42fbd9919cbab8c79189f1971f1765dedf6','historical direct carrier input')
rv=json.loads(review.read_text());need(rv['status']=='PASS_INDEPENDENT_THIRTEEN_LOWDEGREE_SUFFIX_AUDIT' and rv['author_receipt_sha256']==H(receipt) and all('DiophantineConsistency.ModelThirteenForms.standard_equivalence'+str(i) in rv['exact_axiom_names'] for i in (70,71)),'historical audit receipt')
failed=P/'historical-audit-attempt01';need(H(failed/'outer-observation.json')=='f70cd3f75adfccb6cfe4bb86a8bfbe3c7666d3926e1d64657c5612165a185442' and H(failed/'stderr.txt')=='f5c06005e26bc1d86fec04ed7568e55d99169e8f62dcad3275e6077a8bb36c63','failed audit evidence');fo=json.loads((failed/'outer-observation.json').read_text());need(fo['observed_exit']==1 and fo['stderr_sha256']==H(failed/'stderr.txt') and 'HerbrandGeneratedSubmodelTriple.olean' in (failed/'stderr.txt').read_text(),'failed historical replay')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);need(q.returncode==0 and q.stdout==(P/'result.json').read_bytes(),'author rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','profiles':results,'prime':prime,'historical_outer_session':56787,'historical_provider_replayed':False,'scope':'Source-DAG modulo AC and one explicit distributive cut; exact fixed-byte degree; historical recorded endpoints only, no Lean replay or file-to-port theorem.'},sort_keys=True,indent=2))
