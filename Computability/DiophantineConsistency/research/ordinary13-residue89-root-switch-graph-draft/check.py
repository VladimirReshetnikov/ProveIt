#!/usr/bin/env python3
"""Read-only graph-dependency and finite ring controls; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue89-root-switch-graph-draft/Residue89RootSwitchGraph.lean.src': '6f5963feb1ebad8243b0464d4087aeec50471dbc68f447adf8e392d3aa6796e7', 'research/ordinary13-residue89-root-switch-graph-draft/generate.py': '8cd9a606650a12ddb0901a877a00d96af21ea246c07ebaf45dbe68ce1c3a1168', 'research/ordinary13-residue89-root-switch-graph-draft/generated.json': 'ad3452116e34897169bc8b8d5e60eefeda36ad0607d5289fc48c698b7518a332', 'research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src': '01d086c7d25b266f2385d9084f24ee8b9fc15e605eee97503a9b7329396e78f3', 'research/ordinary13-residue-root-switch-extraction-draft/check.py': '37f282aa32ece3c784066bb7728b5eab43cf534c9589caaebf6fd7af89fe4067', 'research/ordinary13-residue-root-switch-extraction-draft/receipt.json': 'def4c853fc953a9ac1da10f85532821bcc1dd3c5d4990ef0f8872ad3e8f1eb73', 'research/ordinary13-residue89-to90-model-draft/Residue89RootSwitchTransport.lean.src': 'f0d0607cd42e6d1226ee498686dd134819cfdbf50f895f27629cb98e09d94c4a', 'research/ordinary13-residue89-to90-model-draft/Residue89To90Transport.lean.src': '8cdbb1809435b9eb09fa930db4e1e13c112ba459aa93d4338d73af2cbf94b0fe', 'research/ordinary13-residue89-to90-model-draft/check.py': 'd15321acac134dee14dc75c389129e53a8c7553716c3606ff2e999513cf32819', 'research/ordinary13-residue89-to90-model-draft/receipt.json': '13d5e7a5b0399453d88ac275c54de85a3cb2a978f266a801deb7305c887e7b55', 'research/ordinary13-residue-folds-model-draft/ResidueFoldP89.lean.src': '1cf3ece1241b09402110f78d7be1712b508e431c763772af5a0f6e91d3bb2a73', 'research/ordinary13-residue-folds-model-draft/ResidueFoldP89Residuals.lean.src': '02849926cb905aa822f0c077329ddef012c8058184ffd719a62c5350a24717c4', 'research/ordinary13-natural-residue-forced89-degree56/candidate.json': 'c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a', 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean': 'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('ordinary13-residue89-root-switch-graph-draft','generate.py','generated.json'),('ordinary13-residue-root-switch-extraction-draft','check.py','receipt.json'),('ordinary13-residue89-to90-model-draft','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
s=(P/'Residue89RootSwitchGraph.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['def putR','first_eval','first_update','unchanged1','unchanged2','unchanged3','replacement_of_scale','J_positive','compact_positiveReplacement','h82 : HAExpressionAssembly.PolynomialBridge']:
 assert x in s,x
j=json.loads((D/'research/ordinary13-natural-residue-forced89-degree56/candidate.json').read_text());rows={r[0]:r for r in j['source']}
def deps(target):
 seen=set();todo=[target]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if n in rows:
   for x in rows[n][2:]:
    if isinstance(x,str):todo.append(x)
 return seen
for t in ['A1','Fam','g72']:assert 'n_r' not in deps(t),t
assert 'n_r' in deps('A0')
def ev(v,p):
 env=dict(zip(j['witnesses'],v));env.update(zip(j['fixed_numerals'],p))
 for n,o,x,y in j['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 return env
rng=random.Random(138982);cases=0
for _ in range(250):
 v=[rng.randrange(0,7) for _ in range(13)];p=[rng.randrange(0,7) for _ in range(4)];w=v.copy();w[8]=rng.randrange(0,10)
 a=ev(v,p);d=ev(w,p);b=v[0]*p[0];q=1+b;Y=q*q*q*(v[7]+1);k=(v[9]+1)+(v[10]+1);ell=v[6]*Y*Y*k;C=q-(v[1]+1)-(v[2]+1);Bt=C*(v[6]+p[1])-(v[1]+1)
 z=b*(ell+k+v[8]-k*Bt)-Bt;znew=b*(ell+k+w[8]-k*Bt)-Bt
 assert a['Z']==z and d['Z']==znew and znew-z==b*(w[8]-v[8])
 assert a['A0']==z*z-b*b*(1+ell*(ell+k)) and all(a[x]==d[x] for x in ('A1','Fam','g72'))
 cases+=1
print(json.dumps({'scope':'source pins and bounded graph dependency controls; no Lean','pinned_files':len(pins),'finite_graph_cases':cases,'nonfirst_residual_r_independence':True,'original_r_positivity_not_claimed':True,'parent_bridge_explicit':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
