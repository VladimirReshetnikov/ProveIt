#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-leibniz-param-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='06ab33d7ce0f638e6e5e095b18498d3b5e568fcb8c4f6c4c02f5f838f50a104c' and sha(p/'source-manifest.json')=='82a91312ee13eda81d674532f9fbde31fe40524a35ec01c3a93ab44b291fb33f'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectLeibnizParam';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectLeibnizNative'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('Semisentenceᵢ language (n+1)','(v : Fin n → Term language ℕ)','Rew.embSubsts (Fin.cons x (Fin.cons y v)) ▹ eqLeft φ =','Rew.embSubsts (Fin.cons x v) ▹ φ','Rew.embSubsts (Fin.cons x (Fin.cons y v)) ▹ eqRight φ =','Rew.embSubsts (Fin.cons y v) ▹ φ','Fin.cases #0 (fun i : Fin n => #i.succ.succ)','Fin.cases #1 (fun i : Fin n => #i.succ.succ)'):assert z in s
native=(root/'Lean/DiophantineConsistency/IPRANativeTheory.lean').read_text();assert 'Rew.subst (Fin.cases #0 (fun i => #i.succ.succ)) ▹ φ' in native and 'Rew.subst (Fin.cases #1 (fun i => #i.succ.succ)) ▹ φ' in native
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-leibniz-native-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'parameterized syntactic rewrites; parameterized native object proof and full sentence equivalence separate'},indent=2))
