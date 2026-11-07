import ast,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed33-jones-compact-macro-prototype'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'build.py':'c529228437b02c15ad1c09ba2694094de312ba32b1009b9df41924758509157e','recipe.json':'06154f18e49d5ac3ca49add3a9b8bb03717f14590d2ef14f892d04b7dc3a75b3','check_structure.py':'9b19ba8e228d749ec849e6d13179708d670788d5f069818b47d323821d2e1b26'}
for n,h in pins.items():assert sha(p/n)==h,n
for cmd in [('build.py','--check'),('check_structure.py',)]:
 x=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/cmd[0]),*cmd[1:]],timeout=30));assert x['recipe_sha256']==pins['recipe.json'] and x['nodes']==45
 if len(cmd)==1:assert x['live_nodes']==45 and x['inputs']==list(range(9)) and x['rejected_mutations']==4
r=json.loads((p/'recipe.json').read_text());assert r['inputs']==9 and r['seed']=='SharingSeed33.seed CurrentWindowCarry2011.ports' and r['seed_type']=='Expr (Fin 34)' and r['coefficient_definitions']=={'z':'ExecutableJones.indexZ seed 0','y':'ExecutableJones.indexY seed 0','pcoef':'ExecutableJones.pCoefficient seed k','expo':'ExecutableJones.codingExpo 33 4 k','star':'ExecutableJones.codingStar 33 4'}
# Independent reference in conventional infix notation. This checks exact
# syntax trees, including subtraction order, all powers and index binders.
L=['pow',['lit',5],['lit',34]]
def nat(x):
 if isinstance(x,ast.Constant) and type(x.value)==int and x.value>=0:return ['lit',x.value]
 if isinstance(x,ast.Name) and x.id=='L':return L
 if isinstance(x,ast.Name) and x.id=='r':return ['index','r']
 if isinstance(x,ast.Call) and isinstance(x.func,ast.Name) and x.func.id=='expo' and len(x.args)==1 and isinstance(x.args[0],ast.Name) and x.args[0].id=='k':return ['expo','k']
 if isinstance(x,ast.BinOp):return [{ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul',ast.Pow:'pow'}[type(x.op)],nat(x.left),nat(x.right)]
 raise ValueError(ast.dump(x))
def ring(x):
 if isinstance(x,ast.Constant) and type(x.value)==int:return ['const',x.value]
 if isinstance(x,ast.Name):
  if x.id in ('z','y'):return ['fixed',x.id]
  if x.id.startswith('a') and x.id[1:].isdigit():return ['var',int(x.id[1:])]
  return ['ref',x.id]
 if isinstance(x,ast.Call) and isinstance(x.func,ast.Name):
  if x.func.id=='pcoef':assert len(x.args)==1 and isinstance(x.args[0],ast.Name) and x.args[0].id=='k';return ['pcoef','k']
  if x.func.id=='star':assert len(x.args)==1;return ['sum_star','k',ring(x.args[0])]
  if x.func.id=='rangeSum':assert len(x.args)==2;return ['sum_range','r',nat(x.args[0]),ring(x.args[1])]
 if isinstance(x,ast.BinOp):
  op={ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul',ast.Pow:'pow'}[type(x.op)]
  return [op,ring(x.left),nat(x.right) if op=='pow' else ring(x.right)]
 raise ValueError(ast.dump(x))
expected=[('b','y+1+a0'),('B','b**5'),('q','B**L'),('N','q**16'),('e','star((z+pcoef(k))*B**(L-expo(k)))'),('ell','rangeSum(33,B**(5**(r+1)))'),('lambda','rangeSum(4*L,B**r)'),('g','a1+1'),('theta','B-2*z'),('G','32*b*B**(5**33)'),('R','(g+e*q**3+ell*q**5+(2*(e-z*lambda_)*(1+B+g)**4+lambda_*B+lambda_*B*q**4)*q**7)*(N**2-N)+(q**3-b*ell+ell+theta*lambda_*q**3+(B-2)*q**8)*(N**2-1)'),('h','a2+1'),('s','a3+1'),('w','a4+1'),('phi','a5'),('i','a6+1'),('j','a7+1'),('t','a8'),('U','N**2*w'),('Y','N**2*s'),('M','R*Y'),('P','2*M**2*U'),('K','R+1+h*(P-1)'),('A','M*(U+1)'),('Bprime','2*R+1'),('W','b*w'),('C','Bprime+W+phi'),('J','4*A-5'),('Q','3*W*C-2*(W**2-1)'),('D','(A**2-1)*C**2+1'),('E','i*J*D*C**2'),('F','(A**2-1)*E**2+1'),('Gprime','A+F*(C*D+1-A)'),('H','Bprime+j*C'),('I','(Gprime**2-1)*H**2+1'),('A0','(P**2-1)*K**2+1'),('A1','D*F*I'),('V0','A0**2+2'),('V1','A1**2+2'),('Bd','(J*F)**2'),('Cd','(Q*F+J*(H-C))**2'),('Dm','K**2*G-4*(C-K*Y)**2*G-8*g*K**2'),('Kc','Bd*(2*Dm-1)'),('T','Bd*t+Cd-Kc*(Cd+V0*V1)'),('output','(T**2+Kc**2*A0-Kc**2*V0**2*A1)**2-4*T**2*Kc**2*A0')]
# Python reserves lambda, map the reference spelling only.
def fix(e):
 if isinstance(e,list):return ['lambda' if i==1 and e[0]=='ref' and x=='lambda_' else fix(x) for i,x in enumerate(e)]
 return e
assert len(expected)==len(r['nodes'])==45
for row,(name,formula) in zip(r['nodes'],expected):
 assert row['name']==name,(row['name'],name)
 expr=fix(ring(ast.parse(formula,mode='eval').body));assert row['expr']==expr,(name,row['expr'],expr)
assert r['output']=='output'

# Preserve byte-level binding of regeneration controls, plus exact ν/seed
# substitution against the already audited 38 named source.
for name,h in {'regeneration.json':'69e81f3479d1222aa96d1d1a39c0bd9fab18456a3fb9f5d0cb6116c47be697b1','structure.json':'5a516acfcef0de9ce1e73d92fcbd6ac25755a34ec1933dd56ceffc24d8ac19bd'}.items():assert sha(p/name)==h
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'build.py'),'--check'],timeout=30)==(p/'regeneration.json').read_bytes()
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check_structure.py')],timeout=30)==(p/'structure.json').read_bytes()
old=(D/'research/nine-seed38-jones-named-formula-check/src/DiophantineConsistency/Norm38NamedFormula.lean').read_text();new=(D/'research/nine-sharing-sign33-jones-named-formula-check/src/DiophantineConsistency/Sign33NamedFormula.lean').read_text()
assert old.replace('Norm38IPRAEndpoint','Sign33IPRAEndpoint').replace('Norm38NamedFormula','Sign33NamedFormula').replace('38-witness','33-witness').replace('let ν := 38','let ν := 33').replace('SharingSeed38.seed','SharingSeed33.seed')==new

print(json.dumps({'status':'PASS_MANUAL_TRANSCRIPTION_AND_INDEPENDENT_NODE_COMPARISON','recipe_sha256':pins['recipe.json'],'nodes_checked':45,'inputs':9,'scope':'Independent human reference transcription compared to JSON and source; structural validator only, no Lean evaluator or machine binding.'},indent=2,sort_keys=True))
