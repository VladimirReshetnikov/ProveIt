#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sha(P/'provider-pins.json')=='7246124bf9bb36d9b8045502583a06627de0cae15fcdbf2ecbd7c454ca4b64bc','pins');pins=json.loads((P/'provider-pins.json').read_text());base=Path('/tmp/nine-sharing-sign15-staged-syntax-check-20261110/lib');out={};extra={}
for family,rec in pins.items():
 d=rec['directory'];root=Path('/tmp')/(d+'-20261110');state=D/'research'/d/'attempt01/state.json';need(sha(state)==rec['state_sha256'],'state '+family);s=json.loads(state.read_text());need(s['status']=='PASS' and len(s['rows'])==(16 if family=='new' else 17),'status '+family)
 for r in s['rows']:
  n=r['module'];need(r['deps']['exit']==0 and r['compile']['exit']==0,'stage '+n);obj=root/'lib/DiophantineConsistency'/(n+'.olean');src=root/'src/DiophantineConsistency'/(n+'.lean');need(sha(obj)==r['object_sha256'] and sha(src)==r['source_sha256'],'producer '+n)
  for k in ('deps','compile'):need(sha(root/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log '+n)
  for k,v in r['direct_guard'].items():
   q=Path(k)
   if v is None:need(not os.path.lexists(q),'unexpected guard '+k)
   else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+k)
  rel='DiophantineConsistency/'+n+'.olean';q=base/rel;item={'realpath':str(obj.resolve()),'sha256':sha(obj)}
  if os.path.lexists(q):need(q.is_file() and str(q.resolve())==item['realpath'] and sha(q)==item['sha256'],'producer collision '+n)
  else:need(family=='old','missing new producer '+n);extra[rel]=item
  if n==rec['module']:out[n]=item
 for k,v in s['overlay_links'].items():
  q=Path(k);b=base/q.relative_to(root/'lib');need(q.is_symlink() and str(q.resolve())==v and b.is_file() and str(b.resolve())==v and sha(b)==sha(q),'overlay mismatch '+k)
need(len(out)==2 and len(extra)==17,'producer count')
print(json.dumps({'status':'PASS','producers':out,'extra':extra,'scope':'two 17-stage producer/union point checks, inherited ancestry'},sort_keys=True))
