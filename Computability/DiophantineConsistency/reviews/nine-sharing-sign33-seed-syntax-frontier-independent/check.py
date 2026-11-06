import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-seed-syntax-draft';sp=D/'research/nine-sharing-quartic65-sign33-candidate/seed.json'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'SharingSeed33Syntax.lean':'80218a4396d553da7c49a2d314a0263643b477db7b14d325874cb3dab595f2dd','generate.py':'a5dab4f2602e31b8adb5681d5180ac60c8a29e75313f0311efe00d232cbe63bf','check.py':'3bab8e30d909363fb4efc98df323b9e7378f6639ad055b97e4f8a896c1e7cb5d','result.json':'43810d0446718fd775915451fae34bc8316390551f2a0aa7b12438716d9e2536'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(sp)=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75';seed=json.loads(sp.read_text());assert seed['coordinate_count']==34 and seed['jones_witness_count']==33 and len(seed['residuals'])==24
s=(p/'SharingSeed33Syntax.lean').read_text();first=s.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 34) :=\n  ',1)[1].splitlines()[0];block=s.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 34)) :=\n  [\n',1)[1].split('\n  ]',1)[0];rows=[first]+[x.strip().removesuffix(',') for x in block.splitlines()];assert len(rows)==24
ports=['beta','K0','MC','MF'];used=set();count=0
def tree(line):
 line=re.sub(r'\(Expr\.constant \(p ([0-3])\)\)',lambda m:'PORT'+m[1],line);line=re.sub(r'\(Expr\.constant \((\d+) : ℤ\)\)',lambda m:'CONST'+m[1],line);line=re.sub(r'\(Expr\.var (\d+)\)',lambda m:'VAR'+m[1],line)
 def dec(node,depth=0):
  global count
  count+=1;assert depth<=80 and count<=100000
  if isinstance(node,ast.Name):
   x=node.id
   if x.startswith('PORT'):return ['port',ports[int(x[4:])]]
   if x.startswith('CONST'):return ['num',int(x[5:])]
   if x.startswith('VAR'):
    i=int(x[3:]);assert 1<=i<=33;used.add(i);return ['var',i]
  if isinstance(node,ast.BinOp):return [{ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}[type(node.op)],dec(node.left,depth+1),dec(node.right,depth+1)]
  raise ValueError(ast.dump(node))
 return dec(ast.parse(line,mode='eval').body)
actual=[tree(x) for x in rows];assert actual==[x['expr'] for x in seed['residuals']]
def deg(t):
 if t[0] in ('num','port'):return 0
 if t[0]=='var':return 1
 a,b=map(deg,t[1:]);return a+b if t[0]=='mul' else max(a,b)
assert max(map(deg,actual))==2 and 0 not in used and all(1<=x<=33 for x in used)
assert [(x['gate'],x['sign']) for x in seed['residuals'] if x['kind']=='signed']==[('gap',1),('tau',1),('cTminusR',1),('V',1),('V2minusY2',-1)]
beta=['add',['port','beta'],['num',1]]
def atzero(t):
 if t[0]=='var':return ['num',0]
 if t[0] in ('num','port'):return t
 op,a,b=t[0],atzero(t[1]),atzero(t[2]);zero=['num',0];one=['num',1]
 if op=='add':return b if a==zero else a if b==zero else [op,a,b]
 if op=='mul':return zero if a==zero or b==zero else b if a==one else a if b==one else [op,a,b]
 return [op,a,b]
assert atzero(actual[0])==['sub',['num',0],['mul',beta,beta]]
assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in s and 'if j = 0 then x else 0' in s
x=subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],timeout=30);assert hashlib.sha256(x).hexdigest()==pins['result.json']
print(json.dumps({'status':'PASS_SOURCE_AST_TRANSCRIPTION_ONLY','pins':pins,'json_sha256':sha(sp),'residuals':len(rows),'ast_nodes':count,'used_coordinates':sorted(used),'first_zero_form':'-(beta+1)^2','scope':'Independent Python AST parse, source-only; no Lean syntax compilation, model bridge, literal port binding or iPRA theorem.'},indent=2,sort_keys=True))
