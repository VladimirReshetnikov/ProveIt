from pathlib import Path
import hashlib,json,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
P=Path('/tmp/arithmetic-dag-rootperm222-peer-p41b9lmc');B=V/'arithmetic-dag-rootperm222-peer-replay'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def require(x,m):
 if not x:raise RuntimeError(m)
require(not B.exists(),'new bundle');B.mkdir();s=json.loads((P/'PEER.json').read_text());require(s['status']=='PASS','passed')
copies=[]
for p in sorted(P.iterdir()):
 if p.is_file():
  dest=B/p.name;shutil.copyfile(p,dest);a,b=rec(p),rec(dest);require(a['sha256']==b['sha256'],'copy');copies.append(dict(original=a,saved=b))
shutil.copyfile(__file__,B/'freeze.py')
for row in s['records']:
 for k in ['source','snapshot','log','timing','object']:
  a=rec(row[k]['path']);require(a['sha256']==row[k]['sha256'],'final '+k)
 row['peak_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',Path(row['timing']['path']).read_text()).group(1))
obs=json.loads((P/'authentication.json').read_text());require(obs['count']==len(obs['observations']),'observations')
save(B/'copies.json',copies)
manifest=[rec(p)for p in sorted(B.iterdir())if p.is_file()]
for m in manifest:m['path']=str(Path(m['path']).relative_to(R))
save(B/'FILES.json',manifest)
packet=dict(status='PASS',reviewer='complemented47_review',scope='Independent complete 534/61 source and mathematical review, exact selected-cache authentication, two fresh private leaf replays. No dependency compilation or source mutation.',author=rec(V/'arithmetic-dag-rootperm222-replay.json'),author_receipt=rec(V/'arithmetic-dag-rootperm222-author.md'),plan=rec(R/'Computability/DiophantineConsistency/research/c222-dag-rootperm222-cache-plan-20261027.json'),private_provider=str(P/'lib'),state=rec(B/'PEER.json'),inputs=rec(B/'inputs.json'),authentication=rec(B/'authentication.json'),driver=rec(B/'driver.py'),manifest=rec(B/'FILES.json'),records=s['records'],counts=s['counts'],observations=s['final_observations'],unique_paths=s['unique_paths'],first_provider_artifacts=590,Foundation_trace_observations=95,free_bytes=s['free_bytes'],failed_peer_attempts=0,qualifications=['Unchanged custom artifacts reuse the authenticated accepted providers; only this pair was compiled.','Package companion pins and Foundation trace rechecks are current observations; this does not rebuild Foundation or package sources.','The earlier failed author attempt remains unchanged in its original evidence packet.','The reviewer previously authored some transitive native/arithmetic215 prerequisites, and earlier independently reviewed Fetch, DagLoops and Control215Table; not author of RootPerm or its new proofs.'])
save(V/'arithmetic-dag-rootperm222-peer-replay.json',packet)
print(json.dumps(dict(packet=rec(V/'arithmetic-dag-rootperm222-peer-replay.json'),manifest=rec(B/'FILES.json'),files=len(manifest),seconds=[x['seconds']for x in s['records']],rss=[x['peak_rss_kib']for x in s['records']],observations=s['final_observations'],paths=s['unique_paths']),indent=2))
