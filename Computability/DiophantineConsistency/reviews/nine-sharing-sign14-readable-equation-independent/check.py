#!/usr/bin/env python3
import ast,contextlib,hashlib,io,json,re,runpy,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-readable-equation';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();receipt=json.loads((p/'result.json').read_text());assert receipt['checker_sha256']==sha(p/'check.py')=='c6f998078ee34253ba24a4bc45f71112fa4122f608053bf32b7c7c5ece14f059' and receipt['presentation_sha256']==sha(p/'README.md')=='ccd1fc27c869904074b223100b39283180f4db3fff5391f94f0695a0e73310b9' and receipt['author_observed_numeric_outer_exit']==0
buf=io.StringIO()
with contextlib.redirect_stdout(buf):g=runpy.run_path(str(p/'check.py'))
o=json.loads(buf.getvalue());assert all(receipt[k]==v for k,v in o.items()) and len(g['verified'])==20 and len(g['roots'])==5
text=(p/'README.md').read_text();assert all(name+'Input' in text for name in ['judge','bound','slack','divisor','factor','index','clock','height','width','count','left','right','target','extra']) and 'Each corresponding shorter name in the formulas is its positive shift' in text
blocks=re.findall(r'```text\n(.*?)\n```',text,re.S);assert len(blocks)==3
names=['judge','bound','slack','divisor','factor','index','clock','height','width','count','left','right','target','extra'];env={name:g['v'][i+1] for i,name in enumerate(names)};env.update({'β':g['BETA'],'K':g['K'],'μ':g['MU'],'ω':g['OMEGA']})
alias_symbols={'base':g['B'],'unit':g['Q'],'horizontal':g['X'],'vertical':g['Y'],'product':g['E'],'center':g['C'],'sum':g['AA'],'weight':g['H'],'delta':g['DELTA'],'root':g['D'],'rank':g['R'],'carry':g['TAU'],'inner':g['V'],'scale':g['SCALE'],'length':g['ELL'],'gap':g['u']+g['vv'],'window':g['Q']-g['F']-g['A']}
expected={'base':g['BETA']*g['J'],'unit':g['B']+1,'window':g['Q']-g['F']-g['A'],'horizontal':g['w']*g['Q'],'vertical':g['h']*g['Q']**3,'product':g['X']*g['Y'],'gap':g['u']+g['vv'],'length':g['E']*(g['u']+g['vv'])*g['Y'],'center':(g['u']+g['vv'])*g['Y']+g['u'],'sum':g['E']+g['Y'],'weight':4*g['AA']+3,'delta':g['AA']**2+g['H'],'root':g['X']+g['AA']*g['C']+g['g']*g['H'],'rank':(g['B']*(g['Q']-g['F'])+g['A'])*(g['Q']**2-1)+(g['MU']+g['Q']*g['OMEGA'])*g['J'],'carry':g['E']*g['n']+g['u']+g['vv']-g['R'],'inner':g['f']**2*(g['C']*g['T']-g['R'])-g['C'],'scale':g['I']*(g['D']**2-1)}
def calc(expr):
 expr=expr.replace('·','*').replace('²','**2').replace('³','**3').replace('−','-')
 def walk(n):
  if isinstance(n,ast.Name):return env[n.id]
  if isinstance(n,ast.Constant) and type(n.value)==int:return g['as_p'](n.value)
  if isinstance(n,ast.BinOp):
   a=walk(n.left);b=walk(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
   if isinstance(n.op,ast.Pow):assert isinstance(n.right,ast.Constant) and type(n.right.value)==int;return a**n.right.value
  raise AssertionError(ast.dump(n))
 return walk(ast.parse(expr,mode='eval').body)
def assignments(block):
 lines=[]
 for line in block.splitlines():
  if '=' in line:lines.append(line.strip())
  else:lines[-1]+=' '+line.strip()
 return [tuple(x.strip() for x in line.split('=',1)) for line in lines]
a=assignments(blocks[0]);assert len(a)==len(expected) and {x for x,y in a}==set(expected)
for name,expr in a:assert calc(expr)==expected[name],name;env[name]=alias_symbols[name]
b=assignments(blocks[1]);assert [n for n,e in b]==['first','second','third','fourth','fifth']
for i,(name,expr) in enumerate(b):g['assert_equal']('display '+name,calc(expr),g['expected'][i]);env[name]=g['S'](name)
assert blocks[2].strip()=='first² + second² + third² + fourth² + fifth² = 0.' or blocks[2].strip()=='first² + second² + third² + fourth² + fifth² = 0'
print(json.dumps({'status':'PASS_EXTERNAL_PRESENTATION_AUDIT','aliases':len(a),'residuals':len(b),'scope':'displayed formulas checked against exact local AST certificate; no Lean JSON/PDF or port-byte binding'},indent=2))
