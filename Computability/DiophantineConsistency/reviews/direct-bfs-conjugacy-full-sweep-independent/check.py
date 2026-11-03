#!/usr/bin/env python3
"""Audit completed full01 author receipts, source/output pins and import resolution; no Lean replay."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'direct-bfs-lean-conjugacy-coverage-prototype';O=P/'observations/full01'; A=R/'direct-bfs-lean-conjugacy-aggregate-prototype'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
manifest='d0847a6276885e969d06cf6c2f3f64b1de1f1cfba71095e35c33393630a57392';runner='81e70123d07fa99d907459ad080cfd059c622f66a7fe4f69e8e340a3e2bef91c';chash='c5b92d5de73775bd9e0e6ef507ba903fd68d093404ab5d30bd64d0af7cdfc36d'
assert sha(P/'coverage-manifest-v2.json')==manifest and sha(P/'run-chunks-v2.py')==runner
m=j(P/'coverage-manifest-v2.json');rs=m['records'];assert len(rs)==59
plan=j(O/'plan.json'); result=j(O/'result.json');out=Path('/tmp/direct-bfs-coverage-full01')
assert plan['start']==result['start']==0 and plan['stop']==result['stop']==59 and result['stages']==59 and result['status']=='PASS_CHUNK_RANGE'
assert plan['runner_sha256']==result['runner_sha256']==runner and plan['manifest_sha256']==result['manifest_sha256']==manifest and plan['output_root']==result['output_root']==str(out)
chunk=plan['selected_import'];assert chunk['module']=='DirectBFSConjugacyChunk' and chunk['sha256']==chash and sha(chunk['path'])==chash
selected=next(Path(x)/'DirectBFSConjugacyChunk.olean' for x in plan['lean_path'].split(':') if (Path(x)/'DirectBFSConjugacyChunk.olean').is_file());assert selected.resolve()==Path(chunk['path']).resolve()
reportcount=0
for i,r in enumerate(rs):
 assert r['index']==i and r['module']==f'DirectBFSCoverage{i:03d}'
 st=O/f'stage-{i:03d}';t=j(st/'terminal.json'); module=r['module'];obj=out/(module+'.olean');orig=P/'chunks-v2'/(module+'.lean');copied=out/(module+'.lean')
 assert t['accepted'] and t['exit']==0 and t['reason'] is None and t['module']==module and t['ranges']==r['ranges'] and t['runner_sha256']==runner
 assert t['direct_import']==chunk and t['object_path']==str(obj) and sha(obj)==t['object_sha256']
 assert sha(orig)==sha(copied)==sha(st/'source.lean')==t['source_sha256']==r['source_sha256']
 assert sha(st/'stdout')==t['stdout_sha256'] and sha(st/'stderr')==t['stderr_sha256']
 logs=(st/'stdout').read_text()+(st/'stderr').read_text()
 assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
 for x in r['ranges']:
  msg=f"'DirectBFSCoverage.{x['kind']}_{i:03d}' does not depend on any axioms";assert logs.count(msg)==1;reportcount+=1
 assert t['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and t['elapsed']<100
 assert len(t['preflight']['lean'])<2 and t['preflight']['available_kib']>=8*1024**2
 assert all(len(s['lean'])<=2 and s['available_kib']>=8*1024**2 for s in t['samples'])
# Frozen reviewed source imports all outputs, and uses exactly the indexed chunk facts in each group.
s=(A/'DirectBFSCoverageAggregate.lean').read_text();imports=re.findall(r'^import\s+(\S+)$',s,re.M)
assert imports==[r['module'] for r in rs]+['DirectBFSConjugacyShape']
kinds=['rows','inverse','horizontal','vertical','inversebounds','horizontalbounds','verticalbounds']
for kind in kinds:
 expected=[f'{kind}_{i:03d}' for i,r in enumerate(rs) if any(x['kind']==kind for x in r['ranges'])]
 actual=re.findall(r'DirectBFSCoverage\.('+kind+r'_\d{3})\b',s)
 assert actual==expected,(kind,len(actual),len(expected))
 assert f'#print axioms DirectBFSCoverageAggregate.{kind}_all' in s
assert not re.search(r'\b(?:sorry|admit)\b',s)
print('PASS full01 summary, 59 stages, source/log/object and direct import; expected axiom lines:',reportcount)
print('plan',sha(O/'plan.json'),'result',sha(O/'result.json'))
print('aggregate source',sha(A/'DirectBFSCoverageAggregate.lean'),'runner under review',sha(A/'run.py'))
print('59 individual stage object/receipt hashes, first through last:')
for i in range(59):
 st=O/f'stage-{i:03d}'/'terminal.json';t=j(st);print(f'{i:03d}',sha(st),t['object_sha256'])
print('No Lean replay; no transitive ancestry claim.')
