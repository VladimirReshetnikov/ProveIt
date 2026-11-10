#!/usr/bin/env python3
"""Prepare direct polynomial exact-degree transport without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here=Path(__file__).resolve().parent;d=here.parents[1]
repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
previous=here.parent/'current14-carrier65-degree-exact-check';check=here.parent/'current14-carrier65-degree-direct-check'
srcdir=check/'src/DiophantineConsistency';srcdir.mkdir(parents=True,exist_ok=True)
sources=[here.parent/'current14-carrier65-degree-upper-draft/Current14Carrier65DegreeUpper.lean',
         here/'Current14Carrier65DegreeDirect.lean']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rows=[]
for source in sources:
 src=srcdir/source.name;shutil.copyfile(source,src)
 rows.append({'module':'DiophantineConsistency.'+src.stem,'source':str(src.relative_to(repo)),
              'source_sha256':sha(src),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)})
manifest=check/'source-manifest.json';manifest.write_text(json.dumps({'rows':rows},indent=2)+'\n')
old=(previous/'run.py').read_text()
old=old.replace("OUT=Path('/tmp/current14-carrier65-degree-exact-20261110')","OUT=Path('/tmp/current14-carrier65-degree-direct-20261110')")
old=re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'",f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'",old)
old=old.replace("need(len(entries)==3,'stage count')","need(len(entries)==2,'stage count')")
start=old.index('replay_sources=');end=old.index('provider_names={r[\'module\']:r for r in base[\'rows\']}',start)
provider=Path('/tmp/current14-carrier65-diagonal-whole-20261110')
pins={}
for n in ['Current14Carrier65OtherFields','Current14Carrier65QActual','Current14Carrier65DiagonalDegree']:
 path=provider/'lib/DiophantineConsistency'/(n+'.olean')
 pins['DiophantineConsistency.'+n]={'realpath':str(path.resolve()),'sha256':sha(path)}
upper=here.parent/'current14-carrier65-degree-upper-check/attempt01/state.json';uouter=upper.parent/'outer-result.json'
uaudit=d/'reviews/current14-carrier65-degree-upper-terminal-independent/check.py'
diag=here.parent/'current14-carrier65-diagonal-degree-retry02-check/attempt01/state.json'
daudit=d/'reviews/current14-carrier65-diagonal-degree-retry02-terminal-independent/check.py'
failures=[]
for name in ['current14-carrier65-degree-exact','current14-carrier65-degree-exact-retry']:
 s=here.parent/(name+'-check/attempt01/state.json');o=s.parent/'outer-result.json';a=d/('reviews/'+name+'-failure-independent/check.py')
 failures.append((str(s),str(o),str(a),sha(s),sha(o),sha(a)))
extra=f'''replay_sources={[(str(s),sha(s)) for s in sources]!r}
for i,(path,digest) in enumerate(replay_sources):
 need(sha(path)==digest and sha(P/'src/DiophantineConsistency'/Path(path).name)==digest,'replay source '+str(i))
upper_state=Path({str(upper)!r});upper_outer=Path({str(uouter)!r});upper_audit=Path({str(uaudit)!r})
upper=json.loads(upper_state.read_text())
need(sha(upper_state)=='{sha(upper)}' and upper['status']=='PASS','upper provider state')
need(len([r for r in upper['rows'] if r['source_sha256']==replay_sources[0][1] and r['compile']['exit']==0])==1,'audited upper replay source')
need(sha(upper_outer)=='{sha(uouter)}' and json.loads(upper_outer.read_text())['outer_exit_code']==0,'upper provider outer')
need(sha(upper_audit)=='{sha(uaudit)}','upper terminal audit')
for state_path,outer_path,audit_path,state_hash,outer_hash,audit_hash in {failures!r}:
 need(sha(state_path)==state_hash and json.loads(Path(state_path).read_text())['status']=='FAILED','prior failed state')
 need(sha(outer_path)==outer_hash and json.loads(Path(outer_path).read_text())['outer_exit_code']==1,'prior failed outer')
 need(sha(audit_path)==audit_hash,'prior failed audit')
extra_pins={pins!r}
diag_state=Path({str(diag)!r});diag_audit=Path({str(daudit)!r});diag=json.loads(diag_state.read_text())
need(sha(diag_state)=='{sha(diag)}' and diag['status']=='PASS' and sha(diag_audit)=='{sha(daudit)}','diagonal transport audit')
matching=[r for r in diag['rows'] if r['module']=='Current14Carrier65DiagonalDegree' and r['compile']['exit']==0]
need(len(matching)==1 and matching[0]['object_sha256']==extra_pins['DiophantineConsistency.Current14Carrier65DiagonalDegree']['sha256'],'diagonal equal-byte point')
for mod,rec in extra_pins.items():
 path=BASE/'lib'/(mod.replace('.','/')+'.olean')
 need(path.is_file() and str(path.resolve())==rec['realpath'] and sha(path)==rec['sha256'],'ingredient point '+mod)
'''
old=old[:start]+extra+old[end:]
old=old.replace('PASS current14 exact polynomial degree','PASS direct conditional exact polynomial degree')
(check/'run.py').write_text(old)
print('Prepared direct polynomial exact-degree transport; no Lean invoked.')
