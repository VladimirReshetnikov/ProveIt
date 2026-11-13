#!/usr/bin/env python3
"""Independently expand shared Lean source text and compare to rendered external AST."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign16-staged-syntax-check';draft=research/'nine-sharing-sign16-staged-syntax-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
candidate=research/'nine-sharing-sign16-degree112-v-candidate/seed.json';assert sha(candidate)=='564ac66abad0fb5e286e5c0c05b5c3cbd05de13e68c9c9ac0b7c3a20a0c0b624';rows=json.loads(candidate.read_text())['residuals'];assert len(rows)==7
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def render(t):
 op,*a=t
 if op=='var':return '(Expr.var '+str(a[0])+')'
 if op=='num':return '(Expr.constant ('+str(a[0])+' : ℤ))'
 if op=='port':return '(Expr.constant (p '+str(ports[a[0]])+'))'
 assert op in ('add','sub','mul') and len(a)==2
 return '('+render(a[0])+' '+{'add':'+','sub':'-','mul':'*'}[op]+' '+render(a[1])+')'
manifest=p/'source-manifest.json';assert sha(manifest)=='03f3f66ce26383a4155ae049135875ab783b4ec8d3799c1255bc37950113f529';entries=json.loads(manifest.read_text())['rows'];names=[f'SharingSeed16Shared{i:02}' for i in range(8)]+[f'SharingSeed16Row{i:02}' for i in range(7)]+['SharingSeed16Degree112','SharingSign16Squares'];assert [e['module'] for e in entries]==['DiophantineConsistency.'+n for n in names]
env={}
def expand(line):
 def replacement(m):
  name=m.group(1);assert name in env;return env[name]
 return re.sub(r'\((shared\d\d) p\)',replacement,line)
for i,(entry,name) in enumerate(zip(entries,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==entry['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 if i<8:
  assert entry['imports']==['DiophantineConsistency.'+('NineFreshJones' if i==0 else names[i-1])]
  for k in range(5*i,min(5*i+5,37)):
   n=f'shared{k:02}';prefix=f'def {n} (p : Fin 4 → ℤ) : Expr (Fin 17) :=\n  ';assert s.count(prefix)==1;env[n]=expand(s.split(prefix,1)[1].splitlines()[0])
 elif i<15:
  assert entry['imports']==['DiophantineConsistency.SharingSeed16Shared07'];j=i-8;prefix=f'def row{j:02} (p : Fin 4 → ℤ) : Expr (Fin 17) :=\n  ';assert s.count(prefix)==1;assert expand(s.split(prefix,1)[1].splitlines()[0])==render(rows[j]['expr'])
 elif i==15:
  assert entry['imports']==['DiophantineConsistency.'+n for n in names[8:15]];assert 'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 17) := row00 p' in s
  assert 'def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 17)) := ['+', '.join(f'row{j:02} p' for j in range(1,7))+']' in s
  assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in s
 else:assert entry['imports']==['DiophantineConsistency.SharingSeed16Degree112','DiophantineConsistency.SharingSign33Squares']
assert len(env)==37
runner=p/'run.py';assert sha(runner)=='1c597239d4eeea70b574d1f7ffb58ccbda6ceef47630b5ec1f2a1ea10f2f66a1';r=runner.read_text();assert "elif local.startswith('SharingSeed16Row') or local.startswith('SharingSeed16Shared'):" in r and "elif local=='SharingSeed16Degree112':" in r and "elif local=='NineFreshJones':" in r and "if local=='SharingSign33Squares':" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','shared_definitions':len(env),'residual_rows':len(rows),'stages':len(names),'runner_sha256':sha(runner),'scope':'source AST expansion and point-provider checks; no Lean result/JSON binding/endpoint'},indent=2,sort_keys=True))
