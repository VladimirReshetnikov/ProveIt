#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-multisubst-retry01-check';old=root/'research/nine-sharing-sign14-positive74-object-multisubst-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='95f84086dbc6bc60fb279494d17570b7d4cbd7d26f7e6d56b94d35974be74f85' and sha(p/'source-manifest.json')=='9c1470732df8d3b8d803d4d085e89111c1bc5a649f6a9294a199cf602595fb30'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectMultiSubst';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCoordinateNative'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s.split('def guardedChain',1)[0]==a.split('def guardedAllSubstitution',1)[0] and s.split('def guardedAllSubstitution',1)[1].split(':= by',1)[0]==a.split('def guardedAllSubstitution',1)[1].split(':= by',1)[0]
for z in ('def guardedChain (g e a b c','((g 🡒 e) 🡒 ((g 🡒 (a 🡒 b)) 🡒 ((e 🡒 (b 🡒 c)) 🡒 (g 🡒 (a 🡒 c)))))','IPRAFunctionCongruenceOpen.update i (w i) (mix s v w) =','Function.update (mix s v w) i (w i)','simpa only [mix_insert, hup]','change extended nativeTheory ⊢ _','simpa only [huniv] using hm Finset.univ'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-multisubst-failure-independent','nine-sharing-sign14-positive74-object-coordinate-native-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'conditional guarded simultaneous substitution retry; object-theory per-coordinate hypotheses explicit'},indent=2))
