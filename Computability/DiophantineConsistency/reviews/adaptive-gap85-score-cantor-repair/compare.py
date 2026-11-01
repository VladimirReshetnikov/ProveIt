#!/usr/bin/env python3
"""Compare two exited Cantor reproductions and freeze their full evidence."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys

D=Path(__file__).resolve().parent
if len(sys.argv)!=3:raise SystemExit('usage: compare.py AUTHOR PEER')
a,b=map(Path,sys.argv[1:]);assert a.resolve()!=b.resolve()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text());mh=H(D/'manifest.json')
sa=json.loads((a/'state.json').read_text());sb=json.loads((b/'state.json').read_text())
for key in ('status','manifest_sha256','source_sha256','direct_imports','original_provider_status',
            'original_failure','exit_code','log_sha256','object_sha256','warnings','scope'):
    assert sa[key]==sb[key],key
assert sa['status']=='PASS' and sa['exit_code']==0 and sa['manifest_sha256']==mh
assert sa['original_provider_status']=='FAILED'
assert sa['object_sha256']==m['expected_olean_sha256'] and sa['log_sha256']==m['old_cantor_log_sha256']
assert len(sa['warnings'])==5
for name in ('ArithmeticCantor.lean','lean.log','BusyBeaver/ZFC/ArithmeticCantor.olean'):
    assert (a/name).read_bytes()==(b/name).read_bytes(),name
assert H(a/'ArithmeticCantor.lean')==m['source_sha256']
assert H(a/'lean.log')==sa['log_sha256'] and H(a/'BusyBeaver/ZFC/ArithmeticCantor.olean')==sa['object_sha256']
for path,digest in m['guard'].items():assert H(path)==digest,path
for records in m['candidates'].values():
    for path,info in records.items():
        p=Path(path)
        if info is None:assert not os.path.lexists(p),path
        else:assert p.is_file() and str(p.resolve())==info['resolved'] and H(p)==info['sha256'],path
for label,src in [('author',a),('peer',b)]:
    dest=D/label;assert not dest.exists(),str(dest);dest.mkdir()
    for name in ('state.json','ArithmeticCantor.lean','lean.log'):
        shutil.copyfile(src/name,dest/name)
    shutil.copyfile(src/'BusyBeaver/ZFC/ArithmeticCantor.olean',dest/'ArithmeticCantor.olean')
old=D/'original-provider';assert not old.exists();old.mkdir()
origin=Path(m['original_provider'])
shutil.copyfile(origin/'state.json',old/'state.json')
for n in ('ArithmeticCantor','Code254'):
    for ext in ('lean','log'):
        shutil.copyfile(origin/'logs/BusyBeaver/ZFC'/(n+'.'+ext),old/(n+'.'+ext))
receipt={'status':'MATCHED_PASS','manifest_sha256':mh,'compare_sha256':H(__file__),
         'author':str(a),'peer':str(b),'author_state_sha256':H(a/'state.json'),
         'peer_state_sha256':H(b/'state.json'),'source_sha256':sa['source_sha256'],
         'object_sha256':sa['object_sha256'],'full_log_sha256':sa['log_sha256'],
         'warnings':sa['warnings'],'selected':m['selected'],
         'candidate_paths':sum(map(len,m['candidates'].values())),
         'original_provider_status':sa['original_provider_status'],'original_failure':sa['original_failure'],
         'scope':m['scope']}
(D/'comparison.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('MATCHED_PASS 2 replays, 500 direct candidates, 5 historical warnings')
