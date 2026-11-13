#!/usr/bin/env python3
"""Review conditional ordered-gap and natural-representative candidates without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-signed-lift-lemmas-retry-check';draft=research/'nine-sharing-sign17-signed-lift-lemmas-retry-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();m=p/'source-manifest.json';assert sha(m)=='c0f55170e46aadc5f8ada45d395d659dad3fe99b30a4754407d6a2dc751a2476';rows=json.loads(m.read_text())['rows'];names=['Sign17OrderedGap','Sign17GapRepresentative'];imports=[['DiophantineConsistency.Sign20CurrentExpressionDef'],['DiophantineConsistency.Sign17OrderedGap']];assert [x['module'] for x in rows]==['DiophantineConsistency.'+n for n in names];texts=[]
for e,n,im in zip(rows,names,imports):
 src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();texts.append(s);assert sha(src)==sha(draft/(n+'.lean'))==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==im and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
a,b=texts;assert all('theorem '+n in a for n in ('root_positive','scale_positive','difference_nonnegative')) and '[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]' in a and '(hb : 0 < beta) (hx : 0 ≤ x) (hr : 0 ≤ rest)' in a
assert '(hF : 1 ≤ F) (hS : 0 < S)' in a and '(hNa : F*F - (S*S)*(F*F - V*V) - 1 = 0)' in a and '0 ≤ F*F - V*V' in a
assert '(hF : 1 ≤ F) (hS : 0 < S)' in b and '∃ gap : V, ι gap = (ι F)*(ι F)-(ι W)*(ι W)' in b and 'nonneg_iff.mp hn' in b
old=research/'nine-sharing-sign17-signed-lift-lemmas-draft'
assert texts[0].replace('[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]','[LinearOrderedCommRing R]')==(old/'Sign17OrderedGap.lean').read_text()
assert texts[1]==(old/'Sign17GapRepresentative.lean').read_text()
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-signed-lift-lemmas-failure-independent/check.py')],check=True,capture_output=True,timeout=120)
runner=p/'run.py';assert sha(runner)=='0ae0eee3264495a5fbb6dc09c18a2702d9e6aec7890909de811355dfb406734c';r=runner.read_text();assert "elif local in ('Sign17OrderedGap',):" in r and "elif local=='Sign20CurrentExpressionDef':" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'stages':2,'scope':'generic ordered-gap positivity and natural representative proposed under explicit hypotheses; no concrete sign17 bridge or Lean result'},indent=2,sort_keys=True))
