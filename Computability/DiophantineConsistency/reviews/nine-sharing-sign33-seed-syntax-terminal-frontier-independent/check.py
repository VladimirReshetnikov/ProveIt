#!/usr/bin/env python3
import hashlib, json, os, re, subprocess, sys
from pathlib import Path
d=Path(__file__).resolve().parents[2]; p=d/'research/nine-sharing-sign33-seed-syntax-check'; a=p/'attempt01'; out=Path('/tmp/nine-sharing-sign33-seed-syntax-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'7aa987d9f52c5b890e6df924baaa1a723789f2c5fd057491872cac1ca24c3d13','SharingSeed33Syntax-compile.txt':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855','outer-observation.json':'69f2c590ea03d5eaa1a7bc26e8bcf2d4a5241e16d558b7af2848160b305875d2'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(62408,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
r=s['rows'][0];assert r['module']=='SharingSeed33Syntax'
assert r['source_sha256']=='80218a4396d553da7c49a2d314a0263643b477db7b14d325874cb3dab595f2dd'
assert r['object_sha256']=='d8d70064be0d7fa609b92a8b51648b6e817096886e0671f37d64271f05e21be0'
source=p/'src/DiophantineConsistency/SharingSeed33Syntax.lean';assert h(source)==r['source_sha256']
assert h(out/'lib/DiophantineConsistency/SharingSeed33Syntax.olean')==r['object_sha256']
assert not re.search(r'^\s*(theorem|lemma)\s',source.read_text(),re.M)
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids']
 assert h(a/('SharingSeed33Syntax-'+k+'.txt'))==x['log_sha256']
assert set(r['dependencies'])=={'Init','DiophantineConsistency.NineFreshJones'}
dep=r['dependencies']['DiophantineConsistency.NineFreshJones'];base=json.loads((d/'research/nine-current-fresh-jones-client/attempt01/state.json').read_text());assert dep['sha256']==base['rows'][0]['object_sha256']
assert r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1055
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
review=d/'reviews/nine-sharing-sign33-seed-syntax-frontier-independent/check.py';assert h(review)=='934ac9b2b352d19a8b0cef7d04f40270a44fd4a9e428dc50df7bc05123a3a245';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS','author_recorded_outer_session':62408,'direct_guards':100,'overlay_links':1055,'scope':'definitions only; external AST comparison; no Lean replay'},sort_keys=True,indent=2))
