#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-coordinate-native-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='1978813ca0c1c70f93c5765efcaf066e649dc38f7e3746e52cc2fbc288103ae5' and sha(p/'source-manifest.json')=='04aa178ffa9a581db451ebcd5b37c0686b084c04f5ccff690fb6b29a3a769f84'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCoordinateNative';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCoordinateFocus'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('extended nativeTheory ⊢! (eqAt (v i) y 🡒','((Rew.embSubsts v ▹ φ) 🡒 (Rew.embSubsts (Function.update v i y) ▹ φ)))','Sign14Positive74ObjectLeibnizParamNative.substitutionOpen','(focusFormula i φ) (v i) y (i.removeNth v)','Function.update v i (v i) = v','simpa only [focus_subst, hv] using h'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-coordinate-focus-terminal-independent','nine-sharing-sign14-positive74-object-leibniz-param-native-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-coordinate-focus-check/attempt01/state.json').read_text());o=json.loads((root/'research/nine-sharing-sign14-positive74-object-leibniz-param-native-check/attempt01/state.json').read_text());k='/tmp/nine-sharing-sign14-positive74-object-coordinate-focus-check-20261110/lib/DiophantineConsistency/Sign14Positive74ObjectLeibnizParamNative.olean';v=b['overlay_links'][k];assert Path(k).resolve()==Path(v).resolve() and sha(Path(v))==o['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native object implication for one arbitrary coordinate update; full iteration separate'},indent=2))
