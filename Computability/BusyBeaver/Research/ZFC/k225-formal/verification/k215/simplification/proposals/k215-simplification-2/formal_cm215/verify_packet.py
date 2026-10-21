#!/usr/bin/env python3
"""Check frozen hashes and literal .tm/Lean/canonical-map correspondence.
This does not substitute for running the supplied Lean build.
"""
from pathlib import Path
import hashlib, json, re
from check_marker_certificate import check, parse

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE/'manifest.json').read_text())
for name, wanted in manifest['files'].items():
    assert hashlib.sha256((HERE/name).read_bytes()).hexdigest() == wanted, name

source = (HERE/'CM215Exact.lean').read_text()
pattern = re.compile(r'  \| (\d+) => if b then some ⟨(true|false), (true|false), (\d+)⟩ else some ⟨(true|false), (true|false), (\d+)⟩')
for name, filename in [('old','k215.native.tm'),('new','cm215.native.tm')]:
    block = source.split('def '+name+' : TM := fun q b =>',1)[1].split('  | _ => none',1)[0]
    table = {}
    for match in pattern.finditer(block):
        q,w1,d1,z1,w0,d0,z0 = match.groups()
        table[int(q),0] = (w0=='true',1 if d0=='true' else -1,int(z0))
        table[int(q),1] = (w1=='true',1 if d1=='true' else -1,int(z1))
    assert len(table)==430 and table == parse(HERE/filename)[1], name

core = (HERE/'CM215Core.lean').read_text().split('def rowsCM',1)[1].split('/-- The alternative',1)[0]
rows = re.findall(r'\(\((true|false), (true|false), (\d+)\), \((true|false), (true|false), (\d+)\)\)',core)
assert len(rows)==215
ctable = {}
for q,row in enumerate(rows):
    for b,(w,d,z) in enumerate((row[:3],row[3:])):
        ctable[q,b] = (w=='true',1 if d=='true' else -1,int(z))
assert ctable == parse(HERE/'cm215.tm')[1]

for base, mapfile, key in [('k215','k215.canonicalization.json','native_to_canonical'),
                           ('cm215','cm215.canonicalization.json','native_to_dense')]:
    mapping = {int(q):int(z) for q,z in json.loads((HERE/mapfile).read_text())[key].items()}
    assert mapping[0]==0 and mapping[254]==215 and len(set(mapping.values()))==216
    native=parse(HERE/(base+'.native.tm'))[1]
    dense=parse(HERE/(base+'.tm'))[1]
    assert {(mapping[q],b):(w,d,mapping[z]) for (q,b),(w,d,z) in native.items()}==dense

pins=json.loads((HERE/'upstream-pins.json').read_text())
for entry in pins['files']:
    assert hashlib.sha256((HERE/entry['local']).read_bytes()).hexdigest()==entry['sha256']
result=check(HERE/'k215.native.tm',HERE/'cm215.native.tm')
print(json.dumps({'status':'PACKET_AND_EXACT_TABLE_BINDINGS_PASS',
                 'files':len(manifest['files']),
                 'working_states':result['working_states'],
                 'compatible_local_cases':result['invariant_compatible_assignments_checked'],
                 'lean_build':'Run build.py separately; recorded successful scope in verification/'},indent=2))
