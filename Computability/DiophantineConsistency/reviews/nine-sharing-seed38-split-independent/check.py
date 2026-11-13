#!/usr/bin/env python3
"""Source, partial retry and provider-route review; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-seed38-split-draft';PREV=D/'research/nine-sharing-norm38-check-retry01';TEMP=Path('/tmp/nine-sharing-norm38-retry01-20261105');BASE=Path('/tmp/nine-fresh-jones-client-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(P/'run.py')=='17dda5818da1a84875d6213cf2b0a080ffce99585294231524199b905998cc0c' and sha(P/'source-manifest.json')=='c4ce5fd28170206e920d1f2f755d995225c40c1eef53d1a0a1d8c76020af03fa' and sha(P/'check.py')=='e1d02ba76fbed3953680dc045bbf8cf2bd26a7ce090b4afeaee5a037a8e5b5e1','current pins')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_SOURCE_ONLY','source checker')
entries=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(entries)==10 and len({x['module'] for x in entries})==10,'manifest unique');seen=set();mods={x['module'] for x in entries}
for e in entries:
 n=e['module'].split('.')[-1];f=P/'src/DiophantineConsistency'/(n+'.lean');need(sha(f)==sha(root/e['source'])==e['source_sha256'],'source '+n);need(re.findall(r'^import ([A-Za-z0-9_.]+)$',f.read_text(),re.M)==e['imports'],'import text '+n)
 for dep in e['imports']:
  if dep in mods:need(dep in seen,'topology '+dep)
 seen.add(e['module'])
need([x['module'].split('.')[-1] for x in entries[:7]]==['SharingGateModel','ForwardWitness38','SharingSeed38Syntax','SharingSeed38Normalize','SharingSeed38Weighted','SharingSeed38Degree','SharingSeed38'],'stage order')
old=(PREV/'run.py').read_text();new=(P/'run.py').read_text();old=old.replace('/tmp/nine-sharing-norm38-retry01-20261105','/tmp/nine-sharing-seed38-split-20261105').replace('932be1171be69ad79a6279b776af15788ee5f9e7a417397e04d94a0608af345d','c4ce5fd28170206e920d1f2f755d995225c40c1eef53d1a0a1d8c76020af03fa').replace('Bounded six-module unverified norm38 model-draft sequence','Bounded ten-module unverified norm38 split model-draft sequence').replace('PASS norm38 draft check sequence','PASS norm38 split draft check sequence');need(new==old,'runner delta')
# The prior two successful outputs are checked as historical observations;
# the new runner recompiles them and does not use these objects as providers.
state=PREV/'attempt01/state.json';need(sha(state)==sha(TEMP/'state.json')=='c50fef5f734b41dadf8455388486c5de86cbe979b2e65cbace72d0d91b95df89','partial retry state');s=json.loads(state.read_bytes());need(s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed SharingSeed38')" and len(s['rows'])==3,'partial status')
for r,expected in zip(s['rows'][:2],['SharingGateModel','ForwardWitness38']):
 n=r['module'];need(n==expected and r['deps']['exit']==r['compile']['exit']==0 and all(r[k]['stop_reason'] is None and not r[k]['monitor_errors'] and not r[k]['observed_descendant_pids'] for k in ('deps','compile')),'prior exits '+n);need(sha(TEMP/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(TEMP/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256'],'prior source/object '+n)
 for typ in ('deps','compile'):need(sha(TEMP/(n+'-'+typ+'.txt'))==sha(PREV/'attempt01'/(n+'-'+typ+'.txt'))==r[typ]['log_sha256'],'prior log '+n)
 for path,v in r['direct_guard'].items():
  f=Path(path)
  if v is None:need(not os.path.lexists(f),'prior absence '+path)
  else:need(f.is_file() and str(f.resolve())==v['realpath'] and sha(f)==v['sha256'],'prior input '+path)
need(s['rows'][1]['dependencies']['DiophantineConsistency.SharingGateModel']['sha256']==s['rows'][0]['object_sha256'],'prior gate route');need(s['rows'][2]['compile']['stop_reason']=='timeout' and not s['rows'][2].get('object_sha256'),'seed timeout')
# The new runner inherits only the Jones provider; reject target-name shadows.
base=json.loads((D/'research/nine-current-fresh-jones-client/attempt01/state.json').read_text());need(base['status']=='PASS' and len(base['rows'])==1,'Jones status')
for e in entries:
 rel=Path(*e['module'].split('.')).with_suffix('.olean');need(not os.path.lexists(BASE/'lib'/rel),'inherited output shadow '+e['module'])
print(json.dumps({'status':'PASS_SCOPED_SOURCE_SPLIT_REVIEW','stage_count':len(entries),'prior_successful_outputs':[s['rows'][0]['object_sha256'],s['rows'][1]['object_sha256']],'scope':'Source split, ordered imports and prior captured object/guard observations. New runner recompiles the two prior outputs; no Lean run, all-model bridge or endpoint.'},indent=2,sort_keys=True))
