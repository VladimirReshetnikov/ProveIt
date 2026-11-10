#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-p-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='cd0a06206bc5b57890503fe96aa51cf73eb6da2db09f2c6b9a1ddcbf16c0783a' and sha(p/'source-manifest.json')=='c17a764cccc164012aaa45a3008cbcc03f18c689774a5f8c3647b2550d73a2f0'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalP';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DiagonalRank','DiophantineConsistency.Current14Carrier65DiagonalCoreBinding'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(axisCore p).k.natDegree = 1','(axisCore p).ell.natDegree = 11','(axisCore p).tau.natDegree = 7','(axisCore p).P.natDegree = 22','(hp : p 0 ≠ 0)','Current14Carrier65DiagonalRank.rank_degree_le p','(d.E * d.k).natDegree = 7','(d.E * (Polynomial.X : P) + d.k - d.rank).natDegree = 7','(d.tau ^ 2 - d.ell * (d.ell + d.k)).natDegree = 22'): assert z in s
for f in ('current14-carrier65-diagonal-rank-terminal-independent','current14-carrier65-diagonal-core-binding-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
a=json.loads((root/'research/current14-carrier65-diagonal-rank-check/attempt01/state.json').read_text());b=json.loads((root/'research/current14-carrier65-diagonal-core-binding-retry-check/attempt01/state.json').read_text())
def relmap(state,base): return {str(Path(k).relative_to(base/'lib')):v for k,v in state['overlay_links'].items()}
aa=relmap(a,Path('/tmp/current14-carrier65-diagonal-rank-20261110'));bb=relmap(b,Path('/tmp/current14-carrier65-diagonal-core-binding-retry-20261110'));ov=set(aa)&set(bb);diff=[x for x in ov if aa[x]!=bb[x]];assert len(ov)==1267 and diff==['DiophantineConsistency/Current14Carrier65QFields.olean'] and sha(Path(aa[diff[0]]))==sha(Path(bb[diff[0]]))=='ffc15e09467d94f0f1c8752c38fbb06579d16b30863fb8954ef0950b5a568f0b'
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual axis k/ell/tau/P exact degrees 1/11/7/22 under p0 nonzero; no whole degree'},indent=2))
