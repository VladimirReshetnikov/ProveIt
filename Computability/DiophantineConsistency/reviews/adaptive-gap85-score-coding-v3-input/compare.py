#!/usr/bin/env python3
"""Compare two fully guarded score v3 runs and freeze their evidence."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
from common import CHECKS, describe, direct_entries, private_inventory, sha, verify_candidates

D=Path(__file__).resolve().parent
if len(sys.argv)!=4:raise SystemExit('usage: compare.py AUTHOR PEER OUTPUT')
a,b,out=map(Path,sys.argv[1:]);assert a.resolve()!=b.resolve() and not os.path.samefile(a/'state.json',b/'state.json')
assert not out.exists()
m=json.loads((D/'manifest.json').read_text());mh=sha(D/'manifest.json');rm=json.loads(Path(m['repair_manifest']).read_text())
states=[json.loads((x/'state.json').read_text()) for x in (a,b)]
def norm(x,root):
    if isinstance(x,str):return x.replace(str(root),'<RUN>')
    if isinstance(x,list):return [norm(y,root) for y in x]
    if isinstance(x,dict):return {norm(k,root):norm(v,root) for k,v in x.items()}
    return x
assert states[0]['status']==states[1]['status']=='PASS'
assert all(s['manifest_sha256']==mh and s['provider']==m['provider'] for s in states)
assert states[0]['records']==states[1]['records']
assert len(states[0]['records'])==2 and all(x['exit']==0 and x['warnings']==0 for x in states[0]['records'])
for field in ('overlay_initial','overlay_final','direct_checks'):
    assert norm(states[0][field],a)==norm(states[1][field],b),field
assert [x['stage'] for x in states[0]['direct_checks']]==['before','after-AdaptiveGap85ScoreCoding','after-AdaptiveGap85ScoreCodingChecks']
for path,info in m['guard'].items():assert describe(path)==info,('guard',path)
for path,digest in rm['guard'].items():assert Path(path).is_file() and sha(path)==digest,('repair guard',path)
for table in rm['candidates'].values():
    for path,info in table.items():
        p=Path(path)
        if info is None:assert not os.path.lexists(p),path
        else:assert p.is_file() and str(p.resolve())==info['resolved'] and sha(p)==info['sha256'],path
P=Path(m['provider']);assert direct_entries(P/'lib')==m['provider_root']
assert direct_entries(P/'lib/DiophantineConsistency')==m['provider_project']
verify_candidates(m['provider_companions']);verify_candidates(m['score_candidates'])
for root,state in zip((a,b),states):
    assert private_inventory(root/'lib')==state['overlay_final']
    assert sha(root/'manifest.json')==mh and sha(root/'driver.py')==m['driver_sha256'] and sha(root/'common.py')==m['common_sha256']
    for row in state['records']:
        name=row['module'];assert sha(root/'src/DiophantineConsistency'/(name+'.lean'))==row['source_sha256']
        assert sha(root/'lib/DiophantineConsistency'/(name+'.olean'))==row['object_sha256']
        assert sha(root/'logs'/(name+'.log'))==row['log_sha256']
    assert (root/'src/DiophantineConsistency/AdaptiveGap85ScoreCodingChecks.lean').read_bytes()==CHECKS
for row in states[0]['records']:
    name=row['module']
    for sub,suffix in (('src/DiophantineConsistency','.lean'),('lib/DiophantineConsistency','.olean'),('logs','.log')):
        assert (a/sub/(name+suffix)).read_bytes()==(b/sub/(name+suffix)).read_bytes(),(name,sub)
out.mkdir(parents=True)
for label,root in (('author',a),('peer',b)):
    dst=out/label;dst.mkdir();(dst/'sources').mkdir();(dst/'objects').mkdir();(dst/'logs').mkdir()
    shutil.copyfile(root/'state.json',dst/'state.json')
    for row in states[0]['records']:
        name=row['module']
        for sub,ext,dest in (('src/DiophantineConsistency','.lean','sources'),('lib/DiophantineConsistency','.olean','objects'),('logs','.log','logs')):
            shutil.copyfile(root/sub/(name+ext),dst/dest/(name+ext))
receipt={'status':'MATCHED_PASS','manifest_sha256':mh,'compare_sha256':sha(__file__),
         'author':str(a),'peer':str(b),'author_state_sha256':sha(a/'state.json'),
         'peer_state_sha256':sha(b/'state.json'),'records':states[0]['records'],
         'direct_stages':[x['stage'] for x in states[0]['direct_checks']],
         'overlay_entries_initial':len(states[0]['overlay_initial']),
         'overlay_entries_final':len(states[0]['overlay_final']),
         'provider_entries':len(m['provider_project']),'provider_companions':len(m['provider_companions']),
         'score_candidates':len(m['score_candidates']),'cantor_candidates':sum(map(len,rm['candidates'].values())),
         'cantor_repair_comparison_sha256':sha(m['repair_receipt']),
         'scope':m['scope']}
(out/'comparison.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('MATCHED_PASS 2 rows, 3 direct-dependency audits,',len(states[0]['overlay_final']),'final overlay entries')
