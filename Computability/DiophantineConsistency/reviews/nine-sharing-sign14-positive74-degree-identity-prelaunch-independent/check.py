#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-degree-identity-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='476a3114869b2035d789d023c661bae3db90e87699c6f515457ad39347a46e80' and sha(p/'source-manifest.json')=='3b71d486abc2b726035ddec1b12df2303269eeb0bbe3a682c764d9dddcecb050'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74DegreeIdentity';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectEndpoint','DiophantineConsistency.Sign14Positive74ExpressionBridge','DiophantineConsistency.ModelCoding'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('MvPolynomial.eval₂ MvPolynomial.C (fun i : Fin 14 => MvPolynomial.X i + 1)','(Sign14Positive74.expression p).toPolynomial','(Sign14Optimized86Expression.expression p).toPolynomial','Sign14Positive74ExpressionBridge.eval_shift','ModelCoding.evalRing_eq_eval₂','MvPolynomial.eval₂_eta'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-endpoint-terminal-independent','nine-sharing-sign14-positive74-expression-bridge-terminal-independent','nine-current-lightweight-jones-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
f=json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],capture_output=True,text=True,check=True,timeout=180).stdout);assert f['status']=='PASS' and f['observed']['Sign14Positive74ExpressionBridge']['sha256']=='c89f008c85b69662144f7aeec81b5487c2833bfec971a79951f9150f379a4a63' and f['observed']['ModelCoding']['sha256']=='b0fda7f05c5bbcfb19d1ef210744ebc3f11ba86f16128545d0348f7a60c471b1'
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed positive74 translation equals natural86 polynomial; degree and external graph/file binding separate'},indent=2))
