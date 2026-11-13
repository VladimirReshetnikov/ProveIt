#!/usr/bin/env python3
"""Independently expand shared Lean source text and compare to rendered external AST."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign14-staged-syntax-check';draft=research/'nine-sharing-sign14-staged-syntax-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
candidate=research/'nine-sharing-sign14-tau-candidate/seed.json';assert sha(candidate)=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';rows=json.loads(candidate.read_text())['residuals'];assert len(rows)==5
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def render(t):
 op,*a=t
 if op=='var':return '(Expr.var '+str(a[0])+')'
 if op=='num':return '(Expr.constant ('+str(a[0])+' : ℤ))'
 if op=='port':return '(Expr.constant (p '+str(ports[a[0]])+'))'
 assert op in ('add','sub','mul') and len(a)==2
 return '('+render(a[0])+' '+{'add':'+','sub':'-','mul':'*'}[op]+' '+render(a[1])+')'
manifest=p/'source-manifest.json';assert sha(manifest)=='b5cb6bf7db5760ece6b06b724195c9392329f5c2e94a9bf2396e5cb391c33701';entries=json.loads(manifest.read_text())['rows'];names=[f'SharingSeed14Shared{i:02}' for i in range(9)]+[f'SharingSeed14Row{i:02}' for i in range(5)]+['SharingSeed14Degree124','SharingSign14Squares'];assert [e['module'] for e in entries]==['DiophantineConsistency.'+n for n in names]
env={}
def expand(line):
 def replacement(m):
  name=m.group(1);assert name in env;return env[name]
 return re.sub(r'\((shared\d\d) p\)',replacement,line)
for i,(entry,name) in enumerate(zip(entries,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==entry['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 if i<9:
  assert entry['imports']==['DiophantineConsistency.'+('NineFreshJones' if i==0 else names[i-1])]
  for k in range(5*i,min(5*i+5,44)):
   n=f'shared{k:02}';prefix=f'def {n} (p : Fin 4 → ℤ) : Expr (Fin 15) :=\n  ';assert s.count(prefix)==1;env[n]=expand(s.split(prefix,1)[1].splitlines()[0])
 elif i<14:
  assert entry['imports']==['DiophantineConsistency.SharingSeed14Shared08'];j=i-9;prefix=f'def row{j:02} (p : Fin 4 → ℤ) : Expr (Fin 15) :=\n  ';assert s.count(prefix)==1;assert expand(s.split(prefix,1)[1].splitlines()[0])==render(rows[j]['expr'])
 elif i==14:
  assert entry['imports']==['DiophantineConsistency.'+n for n in names[9:14]];assert 'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 15) := row00 p' in s
  assert 'def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 15)) := ['+', '.join(f'row{j:02} p' for j in range(1,5))+']' in s
  assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in s
 else:assert entry['imports']==['DiophantineConsistency.SharingSeed14Degree124','DiophantineConsistency.SharingSign33Squares']
assert len(env)==44
runner=p/'run.py';assert sha(runner)=='e694b2780e2a2724190cb14045e08cec75a7efd59d71911a3e0f88178ff8e44e';r=runner.read_text();assert "elif local.startswith('SharingSeed14Row') or local.startswith('SharingSeed14Shared'):" in r and "elif local=='SharingSeed14Degree124':" in r and "elif local=='NineFreshJones':" in r and "if local=='SharingSign33Squares':" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','shared_definitions':len(env),'residual_rows':len(rows),'stages':len(names),'runner_sha256':sha(runner),'scope':'source AST expansion and point-provider checks; no Lean result/JSON binding/endpoint'},indent=2,sort_keys=True))
