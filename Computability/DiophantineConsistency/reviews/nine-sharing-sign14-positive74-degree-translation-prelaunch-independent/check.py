#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-degree-translation-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='6b8cfb200dcea239d6208e3cca9708865bdc694eb9005c1db0bac742441d3d2e' and sha(p/'source-manifest.json')=='5d2a222979a6c2f6f0fb743db2490a21728e506813ac27dc5eab23e075106230'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74DegreeTranslation';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74DegreeSubstBound'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('MvPolynomial.X i + 1','MvPolynomial.X i - 1','untranslate (translate p) = p','MvPolynomial.eval₂_assoc','MvPolynomial.eval₂_eta','(translate p).totalDegree = p.totalDegree','eval₂_degree_le p plusOne plus_degree','eval₂_degree_le (translate p) minusOne minus_degree'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-degree-subst-bound-retry01-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed uniform +1 translation degree preservation via −1 inverse; candidate polynomial degree separate'},indent=2))
