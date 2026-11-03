#!/usr/bin/env python3
"""Audit a recorded incremental author run, without executing Lean."""
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')

HERE = Path(__file__).resolve().parent
COPY = HERE.parent / 'adaptive-qm40-native-incremental-author'
LIVE = Path('/tmp/ipra-qm40-incremental-author-20261102-d')
PINS = {
    'RESULT.json': '3b2ad576262725baf0ad31e68266c9be8d8014f51d4dd905b00e24f5419e5bd0',
    'preflight.json': 'c64c712c72a3940b92797c8d62f972de48642b1a775c96507fd4ad5888d34cc8',
    'IPRAQM40Native.json': '4343544021909931f32cadaa979efadea6e7af49e379fe4c89540736c105ece9',
    'IPRAQM40NativeChecks.json': '73b2b009f61d1ccd82c6974660dbb0c77c77d78e1fb1e12c4f254be9ae45a469',
    'logs/IPRAQM40Native.log': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
    'logs/IPRAQM40NativeChecks.log': '579036fbc93bfb7c87aea8e1e27cfc977eb28cceb0e147148c86d1f64963d9a9',
}

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    require(path.is_file(), 'guard is not a regular file target: '+str(path))
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}

def check_recorded(mapping, label):
    failures = [path for path, expected in mapping.items() if record(path) != expected]
    require(not failures, label+' mismatch: '+str(failures[:3]))

def check_copies():
    for rel, pin in PINS.items():
        require(digest(COPY / rel) == pin and digest(LIVE / rel) == pin,
                'retained/live observation mismatch: '+rel)

check_copies()
pre = json.loads((COPY / 'preflight.json').read_text())
result = json.loads((COPY / 'RESULT.json').read_text())
require(pre['status'] == 'READY_INCREMENTAL_QM40_NO_LEAN' and
        result['status'] == 'PASS_AUTHOR_INCREMENTAL_QM40_NATIVE', 'statuses')
require(result['scope'] == pre['scope'], 'scope drift')
require(len(pre['fixed']) == 23 and len(pre['sources']) == 6 and
        len(result['guards']) == 240, 'recorded guard counts')
check_recorded(pre['fixed'], 'fixed inputs')
check_recorded(pre['sources'], 'native sources')
check_recorded(result['guards'], 'final direct guards')
require(set(pre['guards']).issubset(result['guards']), 'initial guards omitted')

steps = result['steps']
require([s['module'] for s in steps] == ['IPRAQM40Native', 'IPRAQM40NativeChecks'],
        'step inventory')
lib = LIVE / 'lib/DiophantineConsistency'
pkg = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
roots = (LIVE/'lib', Path('/tmp/ipra-qm40-native-author-8thsscoi/lib'), pkg,
         Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'))
suffixes = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')
changed = {p for p,v in pre['guards'].items() if result['guards'][p] != v}
require(changed == {str(lib/'IPRAQM40Native.olean'), str(lib/'IPRAQM40NativeChecks.olean')},
        'unexpected preflight guard change')
expected_direct = [
    {str(pkg/'Init.olean'), str(lib/'AdaptiveQM40Model.olean'), str(lib/'IPRAQF41Native.olean')},
    {str(pkg/'Init.olean'), str(lib/'IPRAQM40Native.olean')},
]
expected_object = ['0ebbc2c26f4f223b827705e6318f22cf65fbf32f3dcdb471776b8dc579b1d262',
                   '3127d1df85bcf39f21ad315eceb4c4d4c953f5b3cacdd9233f68d041cd1f03ae']
for number, step in enumerate(steps):
    name = step['module']
    require(step == json.loads((COPY / (name+'.json')).read_text()) and step['exit'] == 0,
            'individual step receipt: '+name)
    require(set(item['path'] for item in step['direct']) == expected_direct[number],
            'direct dependency set: '+name)
    require(all(record(item['path']) == item['record'] and
                result['guards'].get(item['path']) == item['record'] for item in step['direct']),
            'direct dependency hash or final guard: '+name)
    for item in step['direct']:
        path = Path(item['path'])
        owner = next((root for root in roots if path.is_relative_to(root)), None)
        require(owner is not None, 'dependency outside searched roots')
        relative = path.relative_to(owner)
        stem = str(relative)[:-len('.olean')]
        candidates = []
        for root in roots:
            for suffix in suffixes:
                candidate = str(root / (stem+suffix))
                require(candidate in result['guards'], 'unrecorded dependency candidate: '+candidate)
            candidate = str(root / (stem+'.olean'))
            if result['guards'][candidate] is not None:
                candidates.append((candidate, result['guards'][candidate]))
        require(candidates and candidates[0][0] == str(path) and
                all(v['sha256'] == item['record']['sha256'] for _,v in candidates),
                'search-order or conflicting dependency: '+str(path))
    output = str(lib / (name+'.olean'))
    require(step['output'][output]['sha256'] == expected_object[number] and
            record(output) == step['output'][output], 'output object: '+name)
    require(all(v is None for k,v in step['output'].items() if k != output),
            'unexpected output companion: '+name)
    require(digest(COPY / 'logs' / (name+'.log')) == step['log_sha256'], 'log: '+name)

log = (COPY / 'logs/IPRAQM40NativeChecks.log').read_text()
require(not any(w in log for w in ('sorryAx','error:','warning:')), 'bad checks log')
reports = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.M | re.S)
expected_names = {'DiophantineConsistency.IPRAQM40Native.'+x for x in
                  ('sameNoZero40','bridge40','literal_equivalence')}
require(len(reports) == 3 and {name for name,_ in reports} == expected_names and
        all({x.strip() for x in axioms.split(',')} == {'propext','Classical.choice','Quot.sound'}
            for _,axioms in reports), 'axiom report names or contents')
require((COPY/'logs/IPRAQM40Native.log').read_bytes() == b'', 'unexpected native output')
check_recorded(pre['fixed'], 'fixed inputs after audit')
check_recorded(pre['sources'], 'native sources after audit')
check_recorded(result['guards'], 'final direct guards after audit')
check_copies()
print(json.dumps({'status':'PASS_INDEPENDENT_AUTHOR_ARTIFACT_AUDIT',
                  'fixed':len(pre['fixed']), 'source_records':len(pre['sources']),
                  'final_guards':len(result['guards']), 'modules':len(steps),
                  'axiom_reports':len(reports),
                  'scope':'point-in-time artifact audit; no Lean replay or transitive closure authentication'},
                 sort_keys=True))
