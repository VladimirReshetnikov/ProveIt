from pathlib import Path
from hashlib import sha256
import json, sys, tempfile, subprocess, shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
f80=P('research/ordinary13-unit-product80/candidate.json')
f89=P('research/ordinary13-natural-unit-product89/candidate.json')
a=P('research/ordinary13-natural89-to-positive80-model-draft')
b=P('research/ordinary13-J88-to89-model-draft')
files=[f80,f89,a/'generate.py',a/'PositiveUnit80Graph.lean.src',a/'Natural89Positive80Transport.lean.src',a/'README.md',b/'generate.py',b/'JShifted89Graph.lean.src',b/'J88To89Transport.lean.src',P('Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean'),P('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean')]
text=[p.read_text() for p in files]
g80,g89=map(json.loads,text[:2])
assert len(g80['source'])==80 and len(g89['source'])==89
assert g80['witnesses']==['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma']
assert g89['witnesses']==['n_'+x for x in g80['witnesses']]
assert g80['fixed_numerals']==g89['fixed_numerals']==['beta','K0','MC','MF']
# Verify each inert literal by executing its isolated source generator in a temporary tree.
for gen,inp,out in [(files[2],f80,files[3]),(files[6],f89,files[7])]:
 with tempfile.TemporaryDirectory(prefix='independent-mixed-') as d:
  root=P(d)
  for f in (gen,inp):
   dest=root/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
  subprocess.run([sys.executable,'-I','-S','-B',str(gen)],cwd=root,check=True)
  assert (root/out).read_bytes()==out.read_bytes()
# Hash-cons additive normal forms. Multiplication is an opaque, ordered pair of
# interned expression IDs; no distributivity or finite-field sampling is used.
# Every equality found is valid in any commutative ring.
vecs=[]; vids={}; atoms={}
def vector(d):
 key=tuple(sorted((a,c) for a,c in d.items() if c))
 if key not in vids: vids[key]=len(vecs);vecs.append(key)
 return vids[key]
def atom(key):
 if key not in atoms: atoms[key]=len(atoms)+1
 return atoms[key]
def variable(name): return vector({atom(('variable',name)):1})
def number(n): return vector({0:n})
def add(x,y,sgn=1):
 d=dict(vecs[x])
 for k,v in vecs[y]: d[k]=d.get(k,0)+sgn*v
 return vector(d)
def mul(x,y):
 if not vecs[x] or not vecs[y]: return number(0)
 if len(vecs[x])==1 and vecs[x][0][0]==0:
  return vector({k:vecs[x][0][1]*v for k,v in vecs[y]})
 if len(vecs[y])==1 and vecs[y][0][0]==0: return mul(y,x)
 return vector({atom(('mul',*sorted((x,y)))):1})
def evaluate(g,env):
 env=env.copy()
 for name,op,l,r in g['source']:
  assert name not in env
  x=number(l) if isinstance(l,int) else env[l]
  y=number(r) if isinstance(r,int) else env[r]
  env[name]={'+':lambda:add(x,y),'-':lambda:add(x,y,-1),'*':lambda:mul(x,y)}[op]()
 return env
n={w:variable(w) for w in g89['witnesses']}
ports={p:variable(p) for p in g89['fixed_numerals']}
direct={3,8,11}
p={w:(n['n_'+w] if i in direct else add(n['n_'+w],number(1))) for i,w in enumerate(g80['witnesses'])}
e80=evaluate(g80,{**p,**ports});e89=evaluate(g89,{**n,**ports})
assert e80['k']==e89['k'] and e80['r0']==e89['r0']
assert e80[g80['output']]==e89[g89['output']]
# Deliberately omit each required increment and require the symbolic check to detect it.
for i in sorted(set(range(13))-direct):
 wrong=p.copy(); w=g80['witnesses'][i]; wrong[w]=n['n_'+w]
 assert evaluate(g80,{**wrong,**ports})[g80['output']]!=e89[g89['output']]
s=text[4]
for needle in ['if i=3 ∨ i=8 ∨ i=11 then v i else v i+1','if i=3 ∨ i=8 ∨ i=11 then v i else v i-1','def PositiveDirectReplacement','def DirectFY','def RReplacement','w 3=v 3 ∧ w 11=v 11','theorem replacement_of_cuts','theorem compact_no_zero_iff','theorem compact_sameNoZero','(h80 : PolynomialBridge','EtaUnshift85TransportDraft.ForcedEta K']:
 assert needle in s,needle
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'literal_regeneration_exact':True,'ring_normalized_graph_equality':True,'k_and_r0_equal':True,'direct_coordinates':[3,8,11],'shifted_coordinates':[0,1,2,4,5,6,7,9,10,12],'ten_missing_increment_controls_detected':True,'multiplication_is_not_expanded':True,'lean_executed':False,'limitations':'Source audit only; replacement cuts, exact positive-80 bridge and Lean elaboration remain open.'},sort_keys=True,indent=2))
