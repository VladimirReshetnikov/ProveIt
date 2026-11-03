#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
import json,os,sys,tempfile
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;O=H/'observations/overlay-attempt01';old=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency');fresh=Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib/DiophantineConsistency')
if os.path.lexists(O):raise SystemExit('output exists')
def sha(p):return sha256(p.read_bytes()).hexdigest()
def inventory(root):
 d={}
 for p in root.rglob('*'):
  if p.is_symlink() and not p.is_file():raise RuntimeError('dangling '+str(p))
  if p.is_file():d[str(p.relative_to(root))]={'path':str(p),'target':str(p.resolve(strict=True)),'sha256':sha(p)}
 return d
oldi=inventory(old);newi=inventory(fresh);keys=sorted(set(oldi)|set(newi));shared=sorted(set(oldi)&set(newi));diff=[k for k in shared if oldi[k]['sha256']!=newi[k]['sha256']]
if len(diff)!=5:raise RuntimeError('unexpected overlap differences '+repr(diff))
root=Path(tempfile.mkdtemp(prefix='trace75-oldfirst-overlay-'));ns=root/'DiophantineConsistency';ns.mkdir()
for k in keys:
 rec=oldi.get(k,newi.get(k));p=ns/k;p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(rec['target'])
O.mkdir(parents=True);r={'status':'PASS','root':str(root),'old_root':str(old),'fresh_root':str(fresh),'old':oldi,'fresh':newi,'selected':{k:oldi.get(k,newi.get(k)) for k in keys},'differences':diff,'policy':'old-first per file; fresh fills absent files; exploratory only, no coherent-ancestry claim','script_sha256':sha(Path(__file__))};(O/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'root':str(root),'old':len(oldi),'fresh':len(newi),'shared':len(shared),'differences':diff,'result_sha256':sha(O/'result.json')}))
