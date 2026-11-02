#!/usr/bin/env python3
"""Freeze the four standard-iPRA additions and direct-square endpoint client."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
ROOT=D.parents[3]
BASE=D.parent/'adaptive-aq22-proof/author-additions.json'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df'
ap=argparse.ArgumentParser();ap.add_argument('--source-commit',required=True);a=ap.parse_args()
assert re.fullmatch('[0-9a-f]{40}',a.source_commit)
base=json.loads(BASE.read_text());short=['IPRASuccessorInduction','IPRAAddOneGeneral','IPRASuccessorInductionConverse','IPRAStandardTheory']
names=['DiophantineConsistency.'+x for x in short]+['DiophantineConsistency.IPRAStandardDirect14']
sources={n:base['sources'][n] for n in names[:-1]}
for n in names[:-1]:
 row=sources[n];p=ROOT/row['workspace_path'];b=subprocess.run(['git','show',a.source_commit+':'+row['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
 assert b==p.read_bytes() and hashlib.sha256(b).hexdigest()==row['sha256']
p=D/'draft-src/IPRAStandardDirect14.lean';rel=str(p.relative_to(ROOT))
b=subprocess.run(['git','show',a.source_commit+':'+rel],cwd=ROOT,check=True,capture_output=True).stdout;assert b==p.read_bytes()
imports=re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',b.decode(),re.M)
assert len(imports)==len(set(imports))
sources[names[-1]]={'workspace_path':rel,'sha256':hashlib.sha256(b).hexdigest(),'imports':imports}
reports=['DiophantineConsistency.IPRASquareWitnessDirect14Native.'+x for x in ['sameZero13','bridge13','sameNoZero14','bridge14','literal_equivalence']]
reports += ['DiophantineConsistency.IPRAStandardDirect14.'+x for x in ['literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency']]
declared=re.findall(r'^#print axioms ([A-Za-z_][A-Za-z0-9_.\']*)\s*$',b.decode(),re.M)
assert declared==reports[:5]+[x.rsplit('.',1)[1] for x in reports[5:]]
spec={'status':'FROZEN_ADDITIONS','source_commit':a.source_commit,'order':names,'sources':sources,
      'axiom_reports':{names[-1]:reports},'parent_manifest_sha256':base['parent_manifest_sha256'],
      'scope':'Single-overlay standard-iPRA direct14 author extension of audited historical AQ29 parent; not a paired or current-source replay.'}
out=D/'author-additions.json';raw=(json.dumps(spec,indent=2,sort_keys=True)+'\n').encode()
if out.exists():assert out.read_bytes()==raw
else:out.write_bytes(raw)
print('DIRECT14_FROZEN_MANIFEST',hashlib.sha256(raw).hexdigest())
