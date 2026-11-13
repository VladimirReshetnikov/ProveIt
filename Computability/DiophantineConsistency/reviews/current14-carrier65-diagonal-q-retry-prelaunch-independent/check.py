#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-q-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='60d7db7ea04245c5cd7b59efee112ba88bf51222e5d561ff264abcf5bb6018ec' and sha(p/'source-manifest.json')=='416efa009968bbc6a522dbab9a5dd69b8dae28ad48e7c07b252e67fd24ffd242'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalQ';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DiagonalP','DiophantineConsistency.Current14Carrier65QCancel'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(axisCore p).Q.natDegree = 18','(hp : p 0 ≠ 0)','d.X.natDegree = 2','d.a.natDegree = 6','d.c.natDegree = 5','d.H.natDegree = 6','hroot2','hacroot','hthird','Current14Carrier65QCancel.current_core','Polynomial.natDegree_sub_eq_left_of_natDegree_lt'):assert z in s
old=(root/'research/current14-carrier65-diagonal-q-check/src/DiophantineConsistency/Current14Carrier65DiagonalQ.lean').read_text()
new_block="""    rw [hacroot] at h
    have h' : (Polynomial.C (2 : ℤ) *
        (d.a * d.c * (d.X + (Polynomial.X : P) * d.H))).natDegree = 18 := by
      simpa using h
    simpa only [map_ofNat, mul_assoc] using h'"""
assert old.replace('    simpa [mul_assoc, hacroot] using h',new_block)==s

subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-diagonal-q-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
for f in ('current14-carrier65-diagonal-p-terminal-independent','current14-carrier65-q-actual-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/current14-carrier65-q-actual-retry-check/attempt01/state.json').read_text());qr=[x for x in prior['rows'] if x['module']=='Current14Carrier65QCancel'];assert len(qr)==1 and qr[0]['object_sha256']=='e538015359deef429959f8bd4306c3feb57ac06614e255b777741a4324ecf1d4'
q=Path('/tmp/current14-carrier65-diagonal-p-20261110/lib/DiophantineConsistency/Current14Carrier65QCancel.olean');assert q.is_file() and sha(q)==qr[0]['object_sha256'] and str(q.resolve())=='/tmp/current14-carrier65-q-actual-retry-20261110/lib/DiophantineConsistency/Current14Carrier65QCancel.olean'
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual axis Q degree 18 under p0 nonzero; whole degree separate'},indent=2))
