#!/usr/bin/env python3
"""Receipt and direct graph audit; never runs Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]; P=D/'research/normalized106-fresh-base-model-build'; F=D/'research/normalized106-current14-sixteen-source-preflight/result.json';prod=Path('/tmp/normalized106-fresh-model-build-v2-20261105');out=Path('/tmp/normalized106-fresh-model-client-20261105');base=Path('/tmp/current14-standard-fresh-build-20261104/lib')
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(H(P/'attempt02/state.json')=='c42e5d49c4234ff93e61b7dbadf63fe8e2d465f470f4772879694796d898272c','producer receipt');need(H(P/'attempt03/state.json')=='dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23','client receipt');need(H(F)=='f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2','preflight pin')
need(H(P/'attempt01/state.json')=='666e700df34d562ce6733a95f3c57d2fc0c8b7749d5a8b361776afb4605a1820','first failed state'); first=json.loads((P/'attempt01/state.json').read_text());need(first['status']=='FAILED' and len(first['records'])==8 and 'bad dependency' in first['failure'] and 'Representation.olean' in first['failure'],'first failed attempt')
for n,h in [('attempt01','69716abdf1228496975068fb525d3ae78ae8d718ea2211916936f0d7660166e0'),('attempt02','c239cc011a27d630f9d3b7adefde8a2a2618ad341db023d66aa84a8c9399dbb4'),('attempt03','447490a82e3a69c5fe58742236ff3025c57b451f36de4ea031f416ce3f625394')]:need(H(P/n/'outer-terminal.json')==h,'outer receipt '+n)
r=json.loads((P/'attempt02/state.json').read_text());c=json.loads((P/'attempt03/state.json').read_text());f=json.loads(F.read_text());t=[json.loads((P/x/'outer-terminal.json').read_text()) for x in ('attempt01','attempt02','attempt03')]
need([(x['observed_session'],x['exit_code']) for x in t]==[(80956,1),(13350,1),(52686,0)],'outer exits');need(r['status']=='FAILED' and 'compile failed FreshModel106' in r['failure'] and len(r['records'])==17,'producer terminal');need(c['status']=='PASS' and c['provider_sha256']==H(P/'attempt02/state.json') and c['object_sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','client terminal');need(H(prod/'state.json')==H(P/'attempt02/state.json') and H(out/'state.json')==H(P/'attempt03/state.json'),'external state match')
need(H(P/'build-v2.py')==r['driver_sha256'] and H(P/'check-client.py')==c['driver_sha256'],'runner source');need(H(P/'FreshModel106.lean')==c['source_sha256']=='61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769' and H(out/'FreshModel106.lean')==c['source_sha256'],'client source')
old=(P/'attempt02/FreshModel106.lean').read_text();new=(P/'FreshModel106.lean').read_text();need(new.replace('open ModelCarrierCurrent\n','',1)==old,'targeted source repair');failure=(P/'attempt02/logs/16-FreshModel106-compile.txt').read_text();need('Unknown identifier `expressionAt106`' in failure and 'sorryAx' in failure and r['records'][-1]['compile']['exit']!=0,'failed client')
order=f['extension_order'];need(len(order)==16 and [x['module'] for x in r['records'][:16]]==order,'module ordering');roots=[prod/'lib',Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')];slots=0

def guards(g):
 global slots
 for name,rec in g.items():
  slots+=1;p=Path(name)
  if rec is None:need(not os.path.lexists(p),'unexpected '+name)
  else:need(p.is_file() and str(p.resolve())==rec['realpath'] and H(p)==rec['sha256'],'guard drift '+name)
for idx,rec in enumerate(r['records'][:16]):
 n=rec['module']; s=prod/'src'/(n.replace('.','/')+'.lean');o=prod/'lib'/(n.replace('.','/')+'.olean');need(rec['compile']['exit']==0 and rec['deps_run']['exit']==0 and H(s)==rec['source_sha256']==f['project_sources'][n]['source_sha256'] and H(o)==rec['object_sha256'],'module '+n)
 for typ in ('compile','deps_run'):
  log=Path(rec[typ]['log']);need(H(log)==rec[typ]['log_sha256'],'log '+n+' '+typ);tag='compile' if typ=='compile' else 'deps';copy=P/'attempt02/logs'/f'{idx:02d}-{n.replace(".","_")}-{tag}.txt';need(copy.read_bytes()==log.read_bytes(),'copied log '+n+' '+tag)
 imports=set(f['project_sources'][n]['imports']);need(set(rec['dependencies'])-{'Init'}==imports-{'Init'},'declared imports '+n)
 logs=Path(rec['deps_run']['log']).read_text().splitlines();need(set(logs)==set(rec['dependencies'].values()),'raw deps '+n)
 for dep,path in rec['dependencies'].items():
  q=Path(path);need(q.is_file() and rec['guard'][path]['sha256']==H(q),'selected direct '+n+' '+dep)
  if dep in order:need(dep in order[:idx] and q.is_relative_to(roots[0]) and not q.is_symlink(),'extension order '+dep)
  elif dep in f['project_sources']:need(q.is_relative_to(roots[0]) and q.is_symlink() and q.resolve().is_relative_to(base),'base direct '+dep)
 guards(rec['guard'])
# The corrected endpoint's direct deps and 210 shadow/companion slots.
declared={line.split()[1] for line in new.splitlines() if line.startswith('import ')};need(set(c['dependencies'])-{'Init'}==declared,'corrected client direct imports');need(set((out/'deps.txt').read_text().splitlines())=={x['path'] for x in c['dependencies'].values()},'corrected client raw deps');need(len(c['direct_guard'])==210,'client slots');guards(c['direct_guard'])
for n,rec in c['dependencies'].items():
 q=Path(rec['path']);need(q.is_file() and H(q)==rec['sha256'] and str(q.resolve())==rec['realpath'] and c['direct_guard'][str(q)]['sha256']==H(q),'client direct '+n)
for j,name in enumerate(('deps','compile')):
 record=c['runs'][j];need(record['exit']==0 and H(out/(name+'.txt'))==record['log_sha256'] and (P/'attempt03'/ (name+'.txt')).read_bytes()==(out/(name+'.txt')).read_bytes(),'client '+name)
log=(out/'compile.txt').read_text();need(log.count('depends on axioms:')==3 and log.count('propext')==3 and log.count('Classical.choice')==3 and log.count('Quot.sound')==3 and not any(x in log for x in ('sorryAx','warning:','error:')),'client axioms')
need(H(out/'FreshModel106.olean')==c['object_sha256'],'client object')
need(c['preflight_before_sha256']==c['preflight_after_sha256']==H(F),'preflight hashes');need((out/'preflight-before.json').read_bytes()==F.read_bytes() and (out/'preflight-after.json').read_bytes()==F.read_bytes(),'preflight copies')
links=0
for q in base.rglob('*'):
 if q.is_file():
  z=prod/'lib'/q.relative_to(base);need(z.is_symlink() and z.resolve()==q,'base symlink '+str(z));links+=1
need(links==r['base_symlink_count']==1000,'base link count')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_AUDIT','extension_modules':16,'direct_and_companion_slots_rechecked':slots,'base_symlinks':links,'failure_attempts':[80956,13350],'corrected_client_session':52686,'scope':'Recorded direct source/object/dependency checks. No Lean replay, atomic mutation protection, full dynamic/package-transitive ancestry, or automatic group-RSS enforcement.'},sort_keys=True,indent=2))
