import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-ports-abstract-retry';prior=R/'nine-sharing-norm38-current-ports-split-draft';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();run=q/'run.py';manifest=q/'source-manifest.json'
assert sha(run)=='8ee39d443bc674628c351c08e57f54c5620bb5b48802219a94b5bc7c6eeb0890' and sha(manifest)=='b58ac129649c50eef14df7c1a01181cd8dd248f0598a9344a5a5f4e650082cd9'
rows=json.loads(manifest.read_text())['rows'];names=['Norm38FinFour','Norm38CurrentPortCasts','Norm38CurrentPortSpecialization'];assert [r['module'].split('.')[-1] for r in rows]==names
seen=set();texts=[]
for r in rows:
 n=r['module'].split('.')[-1];p=q/'src/DiophantineConsistency'/f'{n}.lean';assert sha(p)==r['source_sha256'] and D.parents[1]/r['source']==p;t=p.read_text();texts.append(t);assert re.findall(r'^import ([A-Za-z0-9_.]+)$',t,re.M)==r['imports'] and 'sorry' not in t and t.count('#print axioms')==1
 for dep in r['imports']:
  if dep.split('.')[-1] in names:assert dep in seen
 seen.add(r['module'])
t=texts[0];assert 'theorem eq_all {α : Sort*} (f g : Fin 4 → α)' in t and all(f'(h{i} : f {i} = g {i})' in t for i in range(4)) and '∀ j, f j = g j' in t
assert 'Norm38FinFour.eq_all (ringPorts (V := V)) (fun k => ι (naturalPorts (V := V) k))\n    port0 port1 port2 port3 j' in texts[1]
assert texts[2]==(prior/'src/DiophantineConsistency/Norm38CurrentPortSpecialization.lean').read_text()
# Verify runner changes by restoring the handful of intentional hunks.
a=(prior/'run.py').read_text();b=run.read_text()
oldstate="need(sha(STATE)=='ebc30ad19643e6e0fe5eb5f253163d660c8510165e902d53150e11d75a9be578','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1,'bridge state')"
newstate="need(sha(STATE)=='0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='FAILED' and len(base['rows'])==6 and base['rows'][-1]['module']=='Norm38CurrentPortCasts' and base['rows'][-1]['compile']['exit']==1 and base['rows'][-1]['compile']['stop_reason'] is None,'partial state');base['rows']=base['rows'][:5]"
assert oldstate in a
# Replacement must be simultaneous because the new BASE equals the old OUT.
a=a.replace("BASE=Path('/tmp/nine-sharing-norm38-seed-static-iff-check-20261105');OUT=Path('/tmp/nine-sharing-norm38-current-ports-split-20261105')","BASE=Path('/tmp/nine-sharing-norm38-current-ports-split-20261105');OUT=Path('/tmp/nine-sharing-norm38-current-ports-abstract-retry-20261105')").replace("STATE=D/'research/nine-sharing-norm38-seed-static-iff-check/attempt01/state.json'","STATE=D/'research/nine-sharing-norm38-current-ports-split-draft/attempt01/state.json'").replace(oldstate,newstate).replace('868481d10dc1dfd490aec4e34466cce1c90eedb98a1d2d1b196d1686558e9cc7',sha(manifest)).replace('seven-module split current-port cast and static equivalence experiment','three-module abstract Fin4 current-port cast and static equivalence experiment').replace('PASS norm38 split fixed-current-port casts','PASS norm38 abstract fixed-current-port casts');assert a==b
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','manifest_sha256':sha(manifest),'runner_sha256':sha(run),'scope':'No Lean run; abstract theorem and instantiation resource fit untested; failed predecessor excluded.'},indent=2,sort_keys=True))
