#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-numeral-tools-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='3d9883f939ccd34e9e1b62f9118a0acd4981c72e20f52af2d53789c0799731ce' and sha(p/'source-manifest.json')=='a3662ebcd3d83d60a9b2e907442e3438968ba807c79057188e1ea54359da175c'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectNumeralTools';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectMulZeroNative','DiophantineConsistency.IPRAZeroLeft'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('eqAt (.func addCode ![zero,a]) a','IPRAZeroLeft.zero_left','instantiateTheory (T := nativeTheory) IPRAZeroLeft.matrix','eqAt a b 🡒 eqAt b c 🡒 eqAt a c','contextNative _ (trans_context Δ (by simp [Δ]) a b c)'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-mul-zero-native-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],capture_output=True,text=True,check=True,timeout=180);f=json.loads(x.stdout);assert f['status']=='PASS' and f['observed']['IPRAZeroLeft']['sha256']=='1a0a6cece7636fb646b3c259059f103d474cc0a4b81b7e28806e21568d3e6c26'
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native open zero-left and equality transitivity; literal-one normalization and positive leaf separate'},indent=2))
