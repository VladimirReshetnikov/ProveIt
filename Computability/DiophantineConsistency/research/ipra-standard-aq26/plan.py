#!/usr/bin/env python3
"""Produce a source-only single-overlay plan; never reports a Lean replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
BASE = ROOT / 'Computability/DiophantineConsistency/research'
COMMIT = '1eac7a1ac8'  # contains corrected AQ26 drafts and both new client files
PARENT_STATE = Path('/tmp/ipra-aq29-fresh-project-pair/author/state.json')
PARENT_SHA = 'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'

def sha(b): return hashlib.sha256(b).hexdigest()
def load_pinned(path, digest):
    b = path.read_bytes()
    assert sha(b) == digest, path
    return json.loads(b)

aq = load_pinned(BASE/'adaptive-aq28-27-proof/author-additions-v2.json', 'c92c1b41ed0f77c139d83804103c00e61722016d731f7206bfcab088edaecaa9')
std = load_pinned(BASE/'ipra-standard-aq29/author-additions.json', '709a7ed875e813d0403c8f5b970077d2c91eed05406f931166d5b62ea2f72320')
parent = load_pinned(PARENT_STATE, PARENT_SHA)
commit = subprocess.check_output(['git','rev-parse', COMMIT+'^{commit}'],cwd=ROOT,text=True).strip()
names = aq['order'] + std['order'][:4] + ['DiophantineConsistency.IPRAStandardAQ26', 'DiophantineConsistency.IPRAStandardAQ26Checks']
assert len(names)==30 and len(set(names))==30
parent_names = {r['module'] for r in parent['records']}
assert len(parent_names)==1210 and not set(names)&parent_names
assert not any(d in names for r in parent['records'] for d in r['direct_inputs'])
rows = {n:aq['sources'][n] for n in aq['order']}
rows.update({n:std['sources'][n] for n in std['order'][:4]})
for name in names[-2:]:
    path = (HERE/'draft'/(name.rsplit('.',1)[-1]+'.lean')).relative_to(ROOT).as_posix()
    b = (ROOT/path).read_bytes()
    rows[name] = {'workspace_path':path,'sha256':sha(b), 'imports':re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',b.decode(),re.M)}
reports={**aq['axiom_reports']}
reports[names[-1]]=['DiophantineConsistency.IPRAStandardTheory.provable_iff','DiophantineConsistency.IPRAStandardAQ26.literal_equivalence','DiophantineConsistency.IPRAStandardAQ26.selected_foundation_consistency','DiophantineConsistency.IPRAStandardAQ26.literal_iff_translated_consistency']
known=set(parent_names)
for n in names:
    row=rows[n]; path=row['workspace_path']; b=(ROOT/path).read_bytes()
    entry=subprocess.check_output(['git','ls-tree','-z',commit,'--',path],cwd=ROOT)
    head,sep,actual=entry.partition(b'\t')
    assert sep and actual==path.encode()+b'\0' and head.split(b' ')[:2] in ([b'100644',b'blob'],[b'100755',b'blob'])
    pinned=subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
    assert pinned==b and sha(b)==row['sha256']
    imports=re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',b.decode(),re.M)
    assert imports==row['imports'] and all(d in known for d in imports), (n,imports)
    actual_reports=re.findall(r'^#print axioms\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',b.decode(),re.M)
    expected_reports=reports.get(n,[])
    assert len(actual_reports)==len(expected_reports) and all(qualified==short or qualified.endswith('.'+short) for short,qualified in zip(actual_reports,expected_reports)),n
    known.add(n)
assert sum(map(len,reports.values()))==79
spec={'status':'FROZEN_ADDITIONS','source_commit':commit,'parent_manifest_sha256':parent['manifest_sha256'],'order':names,'sources':rows,'axiom_reports':reports,'scope':'Static source-only plan. A fresh single-overlay author run is required; no matched or current-source claim.'}
(HERE/'author-additions.json').write_text(json.dumps(spec,indent=2,sort_keys=True)+'\n')
print('PASS: 30 pinned sources, 79 report names, source-line imports topological; no Lean replay')
