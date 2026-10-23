from pathlib import Path
import ast,json,hashlib,tempfile,shutil,subprocess,os
import sympy as s
R=Path(__file__).resolve().parents[2];P=R/'quartic';O=Path(__file__).resolve().parent
parent=json.loads((P/'quartic42.json').read_text());names=parent['variables']+parent['fixed_numerals'];sy={v:s.Symbol(v)for v in names}
def req(b,m):
 if not b:raise ValueError(m)
def parse(t):
 if isinstance(t,str):return parse(ast.parse(t,mode='eval'))
 if isinstance(t,ast.Expression):return parse(t.body)
 if isinstance(t,ast.Constant)and type(t.value)is int:return s.Integer(t.value)
 if isinstance(t,ast.Name)and t.id in sy:return sy[t.id]
 if isinstance(t,ast.UnaryOp)and isinstance(t.op,ast.USub):return -parse(t.operand)
 if isinstance(t,ast.BinOp):
  a,b=parse(t.left),parse(t.right)
  if isinstance(t.op,ast.Add):return a+b
  if isinstance(t.op,ast.Sub):return a-b
  if isinstance(t.op,ast.Mult):return a*b
  if isinstance(t.op,ast.Pow)and b.is_Integer and 0<=b<=8:return a**b
 raise ValueError('syntax')
old=[parse(x)for x in parent['residuals']];out=[]
idx={'w':22,'X':2,'C2':10,'Delta':9,'F2':14,'Baux':19,'g':17,'L':0,'N':1,'P':6,'E':3}
variants=[('sextic36',['w','C2','F2','Baux','L','E'],36,21,6,{'I':4,'g':2}),('octic32',['w','X','C2','Delta','F2','Baux','g','L','N','P'],32,17,8,{'I':4,'V':4})]
for label,elim,nv,nr,degree,mon in variants:
 d=json.loads((P/(label+'.json')).read_text());req(d['eliminated_monic_coordinates']==elim,'elimination list');remaining=[v for v in parent['variables']if v not in elim];req(remaining==d['variables']and len(remaining)==nv,'variables');req(d['coefficient_binding']==parent['coefficient_binding'],'whole coefficient binding');req(d['fixed_numerals']==parent['fixed_numerals'],'fixed ports');req(d['parent_sha256']==hashlib.sha256((P/'quartic42.json').read_bytes()).hexdigest(),'parent hash')
 recon={sy[k]:parse(v)for k,v in d['reconstruction'].items()};req(set(recon)=={sy[k]for k in elim},'reconstruction keys');req(all(not (v.free_symbols &set(recon))for v in recon.values()),'reconstruction free variables')
 # Independently derive the defining residual coefficient and dependency graph.
 deps={};expr={}
 for v in elim:
  row=old[idx[v]];coeff=s.expand(row).coeff(sy[v]);req(coeff in [-1,1],'unit coefficient '+v);rhs=s.expand(sy[v]-row/coeff);req(sy[v]not in rhs.free_symbols,'no self reference');expr[v]=rhs;deps[v]={u for u in elim if sy[u]in rhs.free_symbols}
 pending=set(elim);done=set();order=[]
 while pending:
  ready={v for v in pending if deps[v]<=done};req(bool(ready),'acyclic definitions');order+=sorted(ready);done|=ready;pending-=ready
 for v in elim:req(s.expand(expr[v].subs(recon,simultaneous=True)-recon[sy[v]])==0,'exact reconstruction '+v)
 deleted={idx[v]for v in elim};transformed=[s.expand(r.subs(recon,simultaneous=True))for r in old];req(all(transformed[i]==0 for i in deleted),'deleted rows vanish');new=[parse(t)for t in d['residuals']];req(len(new)==nr,'row count');expected=[r for i,r in enumerate(transformed)if i not in deleted];req(all(s.expand(a-b)==0 for a,b in zip(new,expected))and len(new)==len(expected),'remaining rows exact')
 vs=[sy[v]for v in remaining];req(max(s.Poly(r,*vs).total_degree()for r in new)*2==degree,'residual degree bound');req(set(remaining)<={str(v)for p in new for v in p.free_symbols},'all variables live')
 allnames=remaining+parent['fixed_numerals'];Q=s.Poly(sum(r*r for r in new),*[sy[v]for v in allnames]);terms=dict(Q.terms());e=json.loads((P/(label+'_expanded.json')).read_text());req(e['variables']==allnames,'expanded order');req(terms=={tuple(t['exponents']):t['coefficient']for t in e['terms']},'expanded polynomial identity');w=tuple(mon.get(v,0)for v in allnames);req(terms.get(w)==1,'degree witness');req([(e,c) for e,c in terms.items() if e[:nv]==w[:nv]]==[(w,s.Integer(1))],'no fixed-port contribution to witness');req(max(sum(e[:nv])for e in terms)==degree,'exact degree')
 out.append({'name':label,'status':'PASS','variables':nv,'residuals':nr,'degree':degree,'terms':len(terms),'acyclic_unit_elimination_order':order,'uniform_leading_witness':mon,'coefficient':1,'unique_integer_reconstruction':True,'whole_coefficient_binding_unchanged':True})
with tempfile.TemporaryDirectory()as t:
 w=Path(t)/'quartic';shutil.copytree(P,w,ignore=shutil.ignore_patterns('__pycache__'))
 for flag in [[],['-O']]:
  p=subprocess.run(['python','-B']+flag+['build_projections.py'],cwd=w,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True);req(p.returncode==0,p.stderr);tag='optimized'if flag else'normal';(O/(tag+'.stdout.txt')).write_text(p.stdout)
  for label,*_ in variants:
   for name in [label+'.json',label+'_expanded.json']:req((P/name).read_bytes()==(w/name).read_bytes(),'byte-identical '+name)
files=['quartic42.json','build_projections.py','sextic36.json','sextic36_expanded.json','octic32.json','octic32_expanded.json']
if (P/'PROJECTIONS.md').exists():files+=['PROJECTIONS.md']
result={'status':'PASS','variants':out,'normal_and_optimized_byte_identical':True,'hashes':{f:hashlib.sha256((P/f).read_bytes()).hexdigest()for f in files}};(O/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
