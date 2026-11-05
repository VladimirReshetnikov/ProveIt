#!/usr/bin/env python3
"""Read-only source, pin and synthetic-control receipt audit; no launch."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2]/'research';d=base/'current14-printed-port-extension-coordinator-v2';v2=base/'current14-printed-port-extension-driver-v2'
pins={d/'coordinator.py':'781b047c5da839917c7f6cfa3c877550f8eba0ef918b0dd08da4480d2a5b6a4c',
 d/'verify.py':'ba46edc8c3e6a48ffeb6afe087462bf798e1371f29a3586b3ac72bda340e6eb0',
 d/'controls.py':'47da56ed2f53bbc46d30b93a7909703d705a7607ff53a92802449e52030b0184',
 d/'controls-observation.json':'36f5ffc12a6f7bae7a40d215d79b99fe075964ecf1db3b061766eec697458ba1',
 v2/'driver.py':'720a5a8ad2bb2cf05dafc5bd68afafbea9f452d343dbfb7e3b77628795492771',
 v2/'guards.py':'e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3',
 v2/'owned.py':'60859f538a7069d90f3f44871613fd2ef96c0ea738c9313cd1971d851b4b33ca'}
for p,h in pins.items():need(sha(p)==h,'pinned file drift '+str(p))
c=json.loads((d/'controls-observation.json').read_text());need(c['status']=='PASS','author controls status')
need(c['coordinator_sha256']==pins[d/'coordinator.py'] and c['verify_sha256']==pins[d/'verify.py'],'author controls source pins')
for k in ('monitor_failure_waits_for_child','emergency_save_and_wait_exceptions_still_wait'):
    need(c['controls'][k] is True,'missing failure control '+k)
need(c['controls']['synthetic_61_row_terminal_accepted']==61,'author synthetic row count')
ind=json.loads((Path(__file__).parent/'nonempty-result.json').read_text())
need(ind['status']=='PASS_SYNTHETIC_NONEMPTY_ROUTES' and ind['verifier_sha256']==pins[d/'verify.py'] and
     ind['guards_sha256']==pins[v2/'guards.py'] and ind['script_sha256']==sha(Path(__file__).parent/'nonempty-controls.py'),
     'independent synthetic receipt pins')
need(ind['controls']['nonempty_61_row_terminal_accepted'] is True and ind['controls']['fresh_project_chain']==60 and
     ind['controls']['direct_base_symlink'] is True and ind['controls']['toolchain_Init'] is True,'synthetic dependency coverage')
out={'status':'PASS_SOURCE_AND_SYNTHETIC_REVIEW','script_sha256':sha(__file__),
 'coordinator_sha256':pins[d/'coordinator.py'],'verifier_sha256':pins[d/'verify.py'],
 'author_controls_sha256':pins[d/'controls-observation.json'],
 'independent_nonempty_result_sha256':sha(Path(__file__).parent/'nonempty-result.json'),
 'driver_sha256':pins[v2/'driver.py'],'guards_sha256':pins[v2/'guards.py'],'owned_sha256':pins[v2/'owned.py'],
 'scope':'Source and synthetic controls only; no launch, actual extension, live base audit or independent process trace.'}
print(json.dumps(out,indent=2,sort_keys=True))
