#!/usr/bin/env python3
import ast,hashlib,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-sextic-lean-draft';J=D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'SharingSeed32Sextic.lean':'83ca02c43152569d1145e32052de74f60e840c16b15e13a55800508fc2c8b0b3','generate.py':'e4ad30861abfaaf9943b54a7c4a8899035bbdfa51fa4cdcbd8b54f4982acb8eb','check.py':'87d74c5b1cf214e58c3813f8462c1f5a0168b81305138f9914565c0658391936','result.json':'05ec66137c443700839fb8d1ab96884c336d7922ae47b03804eea772ce39cb4a','SharingSeed32BridgeDraft.lean':'877303a8541bd851805e86376beba547b75f6f0d420ea547a458dc02bd136ffe','check_bridge.py':'8f733392e537c372627d7120fbd648027703613249773fdae25723ad20cc3a0e','bridge-result.json':'0219847c82fd897b3f12e7e73633361df08ed3a596fdcf351016dafec9536bee'}
for k,v in pins.items():assert sha(P/k)==v,k
assert sha(J)=='f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab'
j=json.loads(J.read_bytes());s=(P/'SharingSeed32Sextic.lean').read_text();b=(P/'SharingSeed32BridgeDraft.lean').read_text()
first=s.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n  ',1)[1].splitlines()[0]
block=s.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 33)) :=\n  [\n',1)[1].split('\n  ]',1)[0];rows=[first]+[x.strip().removesuffix(',') for x in block.splitlines()];assert len(rows)==23
ports=['beta','K0','MC','MF'];used=set()
def parse(line):
 line=re.sub(r'\(Expr\.constant \(p ([0-3])\)\)',lambda m:'PORT'+m[1],line);line=re.sub(r'\(Expr\.constant \((\d+) : ℤ\)\)',lambda m:'CONST'+m[1],line);line=re.sub(r'\(Expr\.var (\d+)\)',lambda m:'VAR'+m[1],line)
 def dec(n):
  if isinstance(n,ast.Name):
   x=n.id
   if x.startswith('PORT'):return ['port',ports[int(x[4:])]]
   if x.startswith('CONST'):return ['num',int(x[5:])]
   if x.startswith('VAR'):
    i=int(x[3:]);assert 1<=i<=32;used.add(i);return ['var',i]
  if isinstance(n,ast.BinOp):return [{ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}[type(n.op)],dec(n.left),dec(n.right)]
  raise ValueError(ast.dump(n))
 return dec(ast.parse(line,mode='eval').body)
assert [parse(r) for r in rows]==[r['expr'] for r in j['residuals']] and used==set(range(1,33))
assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in s
assert 'def zeroWitness (x : ℤ) (j : Fin 33) : ℤ := if j = 0 then x else 0' in s
for name,expected in [('lift',[f'v {i}' for i in range(15)]+['(beta * (v 1 + 1) + 1) ^ 2']+[f'v {i}' for i in range(15,33)]),('drop',[f'v {i}' for i in range(15)]+[f'v {i}' for i in range(16,34)])]:
 m=re.search(r'\bdef '+name+r'\b[^\n]*\n\s*!\[(.*?)\]',b,re.S);assert m and [x.strip() for x in m[1].split(',')]==expected
assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in b and b.count('((p 0 : ℤ) : DiffRing V) = ι beta →')==2
f=b.split('def ForwardTarget',1)[1].split('/-- Open proposition',1)[0]; back=b.split('def BackwardTarget',1)[1]
assert '∀ v : Fin 33 → V' in f and 'InternalZero (SharingSeed32Sextic.seed p) v →' in f and 'InternalZero (SharingSeed33.seed p) (lift beta v)' in f
assert '∀ v : Fin 34 → V' in back and 'InternalZero (SharingSeed33.seed p) v →' in back and 'InternalZero (SharingSeed32Sextic.seed p) (drop v)' in back
assert not re.search(r'^\s*(theorem|lemma)\s',b,re.M) and not re.search(r'\b(sorry|admit)\b',b)
with tempfile.TemporaryDirectory(prefix='sign32-independent-') as tmp:
 root=Path(tmp); p=root/'research/nine-sharing-sign32-sextic-lean-draft'; p.parent.mkdir(); shutil.copytree(P,p)
 jcopy=root/'research/nine-sharing-sign32-sextic-candidate-v2'; jcopy.mkdir(); shutil.copyfile(J,jcopy/'seed.json')
 (p/'SharingSeed32Sextic.lean').unlink()
 for script in ('generate.py','check.py','check_bridge.py'):
  done=subprocess.run([sys.executable,'-I','-S','-B',str(p/script)],cwd=root,capture_output=True,text=True,timeout=30); assert done.returncode==0 and not done.stderr,(script,done.stderr)
  if script in ('generate.py','check.py'):
   out='generation-result.json' if script=='generate.py' else 'result.json'; assert json.loads(done.stdout)==json.loads((P/out).read_text())
 for name in ('SharingSeed32Sextic.lean','generation-result.json','result.json','bridge-result.json'): assert (p/name).read_bytes()==(P/name).read_bytes(),name
assert sha(P/'ERRATUM.md')=='019367d6b1a123bbc655c86608033c5a752d2c8f564157489947c1a4835dbd75'
print(json.dumps({'status':'PASS_SOURCE_ONLY','residuals':23,'coordinate_count':33,'lift_count':34,'drop_count':33,'cast_hypothesis':'port0 integer cast = image of natural-model beta','scope':'independent Python AST parse and source-only bridge targets; no Lean elaboration, bridge theorem, JSON semantics, or endpoint'},indent=2,sort_keys=True))
