#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-leibniz-rewrite-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='a4993d9de57ed7508a2660fe5b0bb880f48108efc26c098409f8fe0273c9916d' and sha(p/'source-manifest.json')=='819b7c8412cab7db2b99e1d60d4a9f101855b12fb4437e6d87b835dc57635479'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectLeibnizRewrite';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCoordinateElim'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('Semisentenceᵢ language 1','Rew.embSubsts ![x,y] ▹ eqLeft φ = Rew.embSubsts ![x] ▹ φ','Rew.embSubsts ![x,y] ▹ eqRight φ = Rew.embSubsts ![y] ▹ φ','Rew.subst (Fin.cases #0 (fun i : Fin 0 => #i.succ.succ))','Rew.subst (Fin.cases #1 (fun i : Fin 0 => #i.succ.succ))'):assert z in s
native=(root/'Lean/DiophantineConsistency/IPRANativeTheory.lean').read_text();assert 'Rew.subst (Fin.cases #0 (fun i => #i.succ.succ)) ▹ φ' in native and 'Rew.subst (Fin.cases #1 (fun i => #i.succ.succ)) ▹ φ' in native
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-coordinate-elim-retry02-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic one-coordinate syntactic substitution identities; no object-theory substitution theorem'},indent=2))
