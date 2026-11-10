#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-leibniz-param-native-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='a0d1f05d570a8fc4e55299391ba7658d4fbeb73c179f5133e9e0e686f39957d7' and sha(p/'source-manifest.json')=='ca3679c265ec5d2cfc95af205a6c89a19f686de16ab5d3ea234a252ddb997daf'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectLeibnizParamNative';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectLeibnizParam'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('Semisentenceᵢ language (n+1)','(v : Fin n → Term language ℕ)','extended nativeTheory ⊢! (eqAt x y 🡒','((Rew.embSubsts (Fin.cons x v) ▹ φ) 🡒 (Rew.embSubsts (Fin.cons y v) ▹ φ)))','NativeAxiom.equality (EqualityAxiomI.substitution φ)','instantiateTheory (T := nativeTheory) (IPRAAllSpecialize.leibnizBody φ) ha','(Fin.cons x (Fin.cons y v))','eqAt, left_rewrite, right_rewrite'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-leibniz-param-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native object-theory equality substitution for one distinguished coordinate and n other parameters'},indent=2))
