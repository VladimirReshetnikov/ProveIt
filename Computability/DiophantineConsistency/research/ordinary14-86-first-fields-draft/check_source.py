#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
g=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes());rows={r[0]:r for r in g['source']}
def leaves(t):
 if t not in rows:return {t}
 _,_,a,b=rows[t];return (leaves(a) if isinstance(a,str) else set()) | (leaves(b) if isinstance(b,str) else set())
assert 'r' in leaves('A0')
for name in ('A1','Fa','g72','guard'):assert 'r' not in leaves(name)
def calc(v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(860101)
for _ in range(300):
 v={x:rng.randint(-5,5) for x in g['witnesses']+g['fixed_numerals']};z=calc(v);b=v['J']*v['beta'];q=1+b;M=q**3*b;k=v['eta']+v['zeta'];ell=v['X']*v['Y']**2*k;pp=ell+k;D0=1+ell*pp
 assert z['A0']==(M*pp+b*v['Y']-M*v['r'])**2-M*M*D0
 v2=v.copy();v2['r']+=13;z2=calc(v2);assert all(z[t]==z2[t] for t in ('A1','Fa','g72','guard'))
s=(P/'FirstFields86.lean').read_text()
for t in ('theorem first_eval','theorem other_fields_ignore_root','theorem fields_of_zero','P86ResidueGraph.graph p','M beta v*firstP v+b beta v*v 7'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name,script in [('ordinary14-residue-guard86-lean-draft','make_graph.py'),('ordinary14-direct-first-root-model-draft','check_source.py')]:
 p=D/'research'/name;args=[sys.executable,'-I','-S','-B',str(p/script)];args+=['--check'] if script=='make_graph.py' else []
 r=subprocess.run(args,cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'FirstFields86.lean',D/'research/ordinary14-residue-guard86-lean-draft/P86ResidueGraph.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean']
print(json.dumps({'scope':'source inventory, dependency cuts, signed first-field controls and draft replays; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
