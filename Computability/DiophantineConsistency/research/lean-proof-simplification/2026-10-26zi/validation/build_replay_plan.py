#!/usr/bin/env python3
"""Generate audit-only copies; never changes measured candidates or sources."""
import hashlib,json,re
from pathlib import Path
from static_audit import mask_noncode
ROOT=Path(__file__).resolve().parents[1]
PREFIX='sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
ORDER=[
 ('WangTiles942FinishConstruction','bridges/candidate/'),
 ('WangTiles942TraceCycle','bridges/candidate/'),
 ('WangTiles942CycleBoundary',PREFIX),
 ('WangTiles942CycleMarker',PREFIX),
 ('WangTiles942HelicalQuotient','helical/proposed/'),
 ('WangTiles942HelicalExtension',PREFIX),
 ('WangTiles942CycleBand','helical/proposed/'),
 ('WangTiles942HelicalMarker',PREFIX),
 ('WangTiles942BandMarker','helical/proposed/'),
]
modules={f'DiophantineConsistency.{n}':f'validation/replay/{n}.lean' for n,_ in ORDER}
records=[]
for name,prefix in ORDER:
 origin=prefix+name+'.lean'; raw=(ROOT/origin).read_text(); code=mask_noncode(raw)
 namespace=re.search(r'^namespace (\S+)$',code,re.M).group(1)
 assert namespace=='DiophantineConsistency.'+name
 expected=[namespace+'.'+n for n in re.findall(r'^(?:theorem|lemma)\s+(\w+)',code,re.M)]
 assert expected and len(expected)==len(set(expected))
 audit='\n-- UNEXECUTED audit commands, excluded from every candidate size metric.\n'+'\n'.join('#print axioms '+n for n in expected)+'\n'
 target=modules[namespace];(ROOT/target).parent.mkdir(exist_ok=True,parents=True);(ROOT/target).write_text(raw+audit)
 imports=[t for line in re.findall(r'^import\s+([^\n]+)',code,re.M) for t in line.split()]
 records.append(dict(source=target,module=namespace,group='composed',origin=origin,
   origin_sha256=hashlib.sha256(raw.encode()).hexdigest(),expected=expected,
   requires_probes=[modules[n] for n in imports if n in modules],
   role='unchanged_connector' if prefix==PREFIX else 'changed_candidate'))
plan=dict(commit='e652d21c413de59e4821f6e8e9b6a3a077bf5bfe',status='UNEXECUTED',
 purpose='One ordered output world; rebuilt connectors prevent stale baseline dependencies.',
 private_helper_audit='halted_tiles_allowed is checked transitively through passTile_allowed and finishTile_allowed; private compiler names are not guessed.',
 probes=records)
(ROOT/'validation/replay_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps({'probes':len(records),'expected_public_theorems':sum(len(p['expected']) for p in records),'lean_executions':0},indent=2))
