#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
rp=D/'research/nine-sharing-sign14-rank-value-check/attempt01/state.json';hp=D/'research/nine-sharing-sign33-windows-retry01/attempt01/state.json';root=Path('/tmp/nine-sharing-sign14-rank-value-check-20261110');base=Path('/tmp/nine-sharing-sign14-transport-row-check-20261110/lib')
need(sha(rp)=='eb69ee3108f12ad6ed86723e949dacbf147abeb6bc3b993be4e193b848e8dbeb' and sha(hp)=='9bba240fcea1e0efc75c9c8022016c61b68a0dfeabb05d66ea4b28786899faa1','state pins');s=json.loads(rp.read_text());need(s['status']=='PASS' and len(s['rows'])==1,'rank status');r=s['rows'][0];n='Sign14RankValue';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'rank stage');obj=root/'lib/DiophantineConsistency'/(n+'.olean');need(sha(obj)==r['object_sha256'] and sha(root/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'],'rank bytes')
for k in ('deps','compile'):need(sha(root/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'rank log')
for k,v in r['direct_guard'].items():
 q=Path(k)
 if v is None:need(not os.path.lexists(q),'guard unexpected '+k)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+k)
for k,v in s['overlay_links'].items():
 q=Path(k);b=base/q.relative_to(root/'lib');need(q.is_symlink() and str(q.resolve())==v and b.is_file() and str(b.resolve())==v and sha(q)==sha(b),'overlay '+k)
h=json.loads(hp.read_text());need(h['status']=='PASS' and len(h['rows'])==1,'historic status');h=h['rows'][0];d=h['dependencies']['DiophantineConsistency.ArithmeticPellFirstIndex'];need(h['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']} and d['sha256']=='20d3769d891a42810c1985203768b122bf936884494d2829415e3140d6deb9c2','historic observation');b=base/'DiophantineConsistency/ArithmeticPellFirstIndex.olean';need(b.is_file() and str(b.resolve())==d['realpath'] and sha(b)==d['sha256'],'first-index current')
print(json.dumps({'status':'PASS','rank_realpath':str(obj.resolve()),'rank_sha256':sha(obj),'first_realpath':d['realpath'],'first_sha256':d['sha256'],'scope':'rank producer and historical first-index point checks, inherited ancestry'},sort_keys=True))
