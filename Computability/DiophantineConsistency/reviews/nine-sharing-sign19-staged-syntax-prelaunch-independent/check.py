#!/usr/bin/env python3
"""Review stage order, independent AST rendering and runner without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign19-staged-syntax-check';draft=research/'nine-sharing-sign19-staged-syntax-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
candidate=research/'nine-sharing-sign19-degree44-y-candidate/seed.json';assert sha(candidate)=='01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1';rows=json.loads(candidate.read_text())['residuals'];assert len(rows)==10
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def render(t):
 op,*a=t
 if op=='var':return '(Expr.var '+str(a[0])+')'
 if op=='num':return '(Expr.constant ('+str(a[0])+' : ℤ))'
 if op=='port':return '(Expr.constant (p '+str(ports[a[0]])+'))'
 assert op in ('add','sub','mul') and len(a)==2
 return '('+render(a[0])+' '+{'add':'+','sub':'-','mul':'*'}[op]+' '+render(a[1])+')'
manifest=packet/'source-manifest.json';assert sha(manifest)=='afcff3eebbc43eef50991470e32ab159e9c32d2e701ce68bb219097d4e97dd24';entries=json.loads(manifest.read_text())['rows'];names=[f'SharingSeed19Row{i:02}' for i in range(10)]+['SharingSeed19Degree44','SharingSign19Squares'];assert [e['module'] for e in entries]==['DiophantineConsistency.'+n for n in names]
for i,(e,n) in enumerate(zip(entries,names)):
 src=packet/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(draft/(n+'.lean'))==e['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 if i<10:
  assert e['imports']==['DiophantineConsistency.NineFreshJones'];assert s.split(f'def row{i:02} (p : Fin 4 → ℤ) : Expr (Fin 20) :=\n  ',1)[1].splitlines()[0]==render(rows[i]['expr'])
 elif i==10:
  assert e['imports']==['DiophantineConsistency.'+n for n in names[:10]];assert 'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 20) := row00 p' in s
  assert 'def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 20)) := ['+', '.join(f'row{j:02} p' for j in range(1,10))+']' in s
  assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in s
 else:
  assert e['imports']==['DiophantineConsistency.SharingSeed19Degree44','DiophantineConsistency.SharingSign33Squares'];assert src.read_bytes()==(research/'nine-sharing-sign19-model-bridge-draft/SharingSign19Squares.lean').read_bytes()
runner=packet/'run.py';assert sha(runner)=='a105ba3a9468d226a0e2e7d10f9b1a3540fec0074a84c8bb4d70b0bdf231a714';r=runner.read_text();assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "elif local.startswith('SharingSeed19Row'):" in r and "elif local=='SharingSeed19Degree44':" in r and "elif local=='NineFreshJones':" in r and "if local=='SharingSign33Squares':" in r
assert "need(not OUT.exists(),'output exists')" in r and "final provider drift" in r
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','rows_independently_rendered':10,'stages':12,'runner_sha256':sha(runner),'scope':'source-only transcription and guard check; no Lean result or endpoint'},indent=2,sort_keys=True))
