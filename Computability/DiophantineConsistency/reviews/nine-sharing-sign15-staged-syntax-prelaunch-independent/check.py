#!/usr/bin/env python3
"""Independently expand shared Lean source text and compare to rendered external AST."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign15-staged-syntax-check';draft=research/'nine-sharing-sign15-staged-syntax-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
candidate=research/'nine-sharing-sign15-inner-candidate/seed.json';assert sha(candidate)=='bdd841f25618a01e659d6f2f802f0420501b00c5270df9fa56b9589733ecbd59';rows=json.loads(candidate.read_text())['residuals'];assert len(rows)==6
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def render(t):
 op,*a=t
 if op=='var':return '(Expr.var '+str(a[0])+')'
 if op=='num':return '(Expr.constant ('+str(a[0])+' : ℤ))'
 if op=='port':return '(Expr.constant (p '+str(ports[a[0]])+'))'
 assert op in ('add','sub','mul') and len(a)==2
 return '('+render(a[0])+' '+{'add':'+','sub':'-','mul':'*'}[op]+' '+render(a[1])+')'
manifest=p/'source-manifest.json';assert sha(manifest)=='b983e8c1f5d2d2204b10cf0ed7f31d1a516abdb916230e6df2f4c6c7dbb3da42';entries=json.loads(manifest.read_text())['rows'];names=[f'SharingSeed15Shared{i:02}' for i in range(8)]+[f'SharingSeed15Row{i:02}' for i in range(6)]+['SharingSeed15Degree124','SharingSign15Squares'];assert [e['module'] for e in entries]==['DiophantineConsistency.'+n for n in names]
env={}
def expand(line):
 def replacement(m):
  name=m.group(1);assert name in env;return env[name]
 return re.sub(r'\((shared\d\d) p\)',replacement,line)
for i,(entry,name) in enumerate(zip(entries,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==entry['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 if i<8:
  assert entry['imports']==['DiophantineConsistency.'+('NineFreshJones' if i==0 else names[i-1])]
  for k in range(5*i,min(5*i+5,40)):
   n=f'shared{k:02}';prefix=f'def {n} (p : Fin 4 → ℤ) : Expr (Fin 16) :=\n  ';assert s.count(prefix)==1;env[n]=expand(s.split(prefix,1)[1].splitlines()[0])
 elif i<14:
  assert entry['imports']==['DiophantineConsistency.SharingSeed15Shared07'];j=i-8;prefix=f'def row{j:02} (p : Fin 4 → ℤ) : Expr (Fin 16) :=\n  ';assert s.count(prefix)==1;assert expand(s.split(prefix,1)[1].splitlines()[0])==render(rows[j]['expr'])
 elif i==14:
  assert entry['imports']==['DiophantineConsistency.'+n for n in names[8:14]];assert 'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 16) := row00 p' in s
  assert 'def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 16)) := ['+', '.join(f'row{j:02} p' for j in range(1,6))+']' in s
  assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in s
 else:assert entry['imports']==['DiophantineConsistency.SharingSeed15Degree124','DiophantineConsistency.SharingSign33Squares']
assert len(env)==40
runner=p/'run.py';assert sha(runner)=='d618c33828ad44d26214c3647623f739ff6aad75232b09592b0b0f432704338d';r=runner.read_text();assert "elif local.startswith('SharingSeed15Row') or local.startswith('SharingSeed15Shared'):" in r and "elif local=='SharingSeed15Degree124':" in r and "elif local=='NineFreshJones':" in r and "if local=='SharingSign33Squares':" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','shared_definitions':len(env),'residual_rows':len(rows),'stages':len(names),'runner_sha256':sha(runner),'scope':'source AST expansion and point-provider checks; no Lean result/JSON binding/endpoint'},indent=2,sort_keys=True))
