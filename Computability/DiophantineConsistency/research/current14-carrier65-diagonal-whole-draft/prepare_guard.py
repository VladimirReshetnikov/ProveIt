#!/usr/bin/env python3
"""Prepare whole diagonal degree replay/assembly without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here=Path(__file__).resolve().parent;d=here.parents[1]
repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
previous=here.parent/'current14-carrier65-q-actual-check';check=here.parent/'current14-carrier65-diagonal-whole-check'
srcdir=check/'src/DiophantineConsistency';srcdir.mkdir(parents=True,exist_ok=True)
sources=[here.parent/'current14-carrier65-diagonal-w-retry02-draft/Current14Carrier65DiagonalW.lean',
         here.parent/'current14-carrier65-diagonal-q-retry-draft/Current14Carrier65DiagonalQ.lean',
         here/'Current14Carrier65DiagonalWhole.lean']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rows=[]
for source in sources:
 src=srcdir/source.name;shutil.copyfile(source,src)
 rows.append({'module':'DiophantineConsistency.'+src.stem,'source':str(src.relative_to(repo)),
              'source_sha256':sha(src),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)})
manifest=check/'source-manifest.json';manifest.write_text(json.dumps({'rows':rows},indent=2)+'\n')
provider=Path('/tmp/current14-carrier65-diagonal-uz-20261110')
state=here.parent/'current14-carrier65-diagonal-uz-check/attempt01/state.json';outer=state.parent/'outer-result.json'
audit=d/'reviews/current14-carrier65-diagonal-uz-terminal-independent/check.py'
old=(previous/'run.py').read_text()
old=old.replace("BASE=Path('/tmp/current14-carrier65-q-fields-20261110')",f"BASE=Path({str(provider)!r})")
old=old.replace("OUT=Path('/tmp/current14-carrier65-q-actual-20261110')","OUT=Path('/tmp/current14-carrier65-diagonal-whole-20261110')")
start=old.index("STATE=D/'research/current14-carrier65-q-fields-check/attempt01/state.json'");end=old.index('\nroots=',start)
old=old[:start]+("STATE=D/'research/current14-carrier65-diagonal-uz-check/attempt01/state.json';"
                "OUTER=STATE.parent/'outer-result.json';AUDIT=D/'reviews/current14-carrier65-diagonal-uz-terminal-independent/check.py'")+old[end:]
old=re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'",f"need(sha(STATE)=='{sha(state)}'",old)
old=re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'",f"need(sha(OUTER)=='{sha(outer)}'",old)
old=re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'",f"need(sha(AUDIT)=='{sha(audit)}'",old)
old=old.replace("base['rows'][-1]['module']=='Current14Carrier65QFields'","base['rows'][-1]['module']=='Current14Carrier65DiagonalUZ'")
old=re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'",f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'",old)
start=old.index('replay_sources=');end=old.index('provider_names={r[\'module\']:r for r in base[\'rows\']}',start)
pins={}
for n in ['Current14Carrier65DiagonalBinding','Current14Carrier65DiagonalP','Current14Carrier65QCancel']:
 path=provider/'lib/DiophantineConsistency'/(n+'.olean')
 pins['DiophantineConsistency.'+n]={'realpath':str(path.resolve()),'sha256':sha(path)}
replays=[]
for name in ['current14-carrier65-diagonal-w-retry02','current14-carrier65-diagonal-q-retry']:
 s=here.parent/(name+'-check/attempt01/state.json');o=s.parent/'outer-result.json';a=d/('reviews/'+name+'-terminal-independent/check.py')
 replays.append((str(s),str(o),str(a),sha(s),sha(o),sha(a)))
extra=f'''replay_sources={[(str(s),sha(s)) for s in sources]!r}
for i,(path,digest) in enumerate(replay_sources):
 need(sha(path)==digest and sha(P/'src/DiophantineConsistency'/Path(path).name)==digest,'replay source '+str(i))
for i,(state_path,outer_path,audit_path,state_hash,outer_hash,audit_hash) in enumerate({replays!r}):
 replay=json.loads(Path(state_path).read_text())
 need(sha(state_path)==state_hash and replay['status']=='PASS','replay provider state')
 matching=[r for r in replay['rows'] if r['source_sha256']==replay_sources[i][1] and r['compile']['exit']==0]
 need(len(matching)==1,'audited replay source '+str(i))
 need(sha(outer_path)==outer_hash and json.loads(Path(outer_path).read_text())['outer_exit_code']==0,'replay provider outer')
 need(sha(audit_path)==audit_hash,'replay terminal audit')
extra_pins={pins!r}
for mod,rec in extra_pins.items():
 path=BASE/'lib'/(mod.replace('.','/')+'.olean')
 need(path.is_file() and str(path.resolve())==rec['realpath'] and sha(path)==rec['sha256'],'ingredient point '+mod)
'''
old=old[:start]+extra+old[end:]
old=old.replace('PASS current14 actual Q degree upper bound','PASS current14 whole diagonal degree')
(check/'run.py').write_text(old)
print('Prepared whole diagonal degree; no Lean invoked.')
