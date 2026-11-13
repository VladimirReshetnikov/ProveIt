#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-multisubst-retry02-check';old=root/'research/nine-sharing-sign14-positive74-object-multisubst-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f26a6cee322470017fc9350912b6e9f07dd51092d6d809a262c54321c56d4edd' and sha(p/'source-manifest.json')=='b8952b78dc0159a1f1cb323ef74e1f67b4a86951f059df233c5476e4c2232a58'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectMultiSubst';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCoordinateNative'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s.split('def guardedChain',1)[0]==a.split('def guardedChain',1)[0] and s.split('def guardedAllSubstitution',1)[1].split(':= by',1)[0]==a.split('def guardedAllSubstitution',1)[1].split(':= by',1)[0]
for z in ('(he : extended nativeTheory ⊢! (g 🡒 e))','(hab : extended nativeTheory ⊢! (g 🡒 (a 🡒 b)))','(step : extended nativeTheory ⊢! (e 🡒 (b 🡒 c)))','let Γ : List (Propositionᵢ language) := [a,g]','Entailment.FiniteContext.byAxm₀','Entailment.FiniteContext.byAxm₁','(Entailment.FiniteContext.of step) ⨀ he\' ⨀ hb','he (Classical.choice ih) step','simpa only [mix_insert, hup] using t'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-multisubst-failure-independent','nine-sharing-sign14-positive74-object-multisubst-retry01-failure-independent','nine-sharing-sign14-positive74-object-coordinate-native-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'conditional guarded simultaneous substitution retry using finite context'},indent=2))
