#!/usr/bin/env python3
"""Freeze a joint historical-parent extension for both 13-variable endpoints."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent;ROOT=D.parents[3];BASE=D.parent/'adaptive-aq22-proof/author-additions.json'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df'
ap=argparse.ArgumentParser();ap.add_argument('--source-commit',required=True);a=ap.parse_args();assert re.fullmatch('[0-9a-f]{40}',a.source_commit)
base=json.loads(BASE.read_text());short=['IPRASuccessorInduction','IPRAAddOneGeneral','IPRASuccessorInductionConverse','IPRAStandardTheory',
 'AdaptiveDirectOrdinateSquareSumsLiteral','IPRASquareSumsNative','IPRAStandardSquareSums13','IPRAStandardProduct13']
names=['DiophantineConsistency.'+x for x in short];sources={n:base['sources'][n] for n in names[:4]}
for n in names[:4]:
 row=sources[n];p=ROOT/row['workspace_path'];b=subprocess.run(['git','show',a.source_commit+':'+row['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
 assert b==p.read_bytes() and hashlib.sha256(b).hexdigest()==row['sha256']
for n,shortname in zip(names[4:],short[4:]):
 p=D/'draft-src'/(shortname+'.lean');rel=str(p.relative_to(ROOT));b=subprocess.run(['git','show',a.source_commit+':'+rel],cwd=ROOT,check=True,capture_output=True).stdout;assert b==p.read_bytes()
 imports=re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',b.decode(),re.M);assert len(imports)==len(set(imports))
 sources[n]={'workspace_path':rel,'sha256':hashlib.sha256(b).hexdigest(),'imports':imports}
reports={names[6]:['DiophantineConsistency.IPRASquareSumsNative.'+x for x in ['sameZero','bridge','equivalence','literal_eq','literal_equivalence']]+[names[6]+'.'+x for x in ['literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency']],
 names[7]:['DiophantineConsistency.HAAdaptiveDirectOrdinate86.polynomialBridge']+[names[7]+'.'+x for x in ['native_equivalence','literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency']]}
for n in reports:
 text=(ROOT/sources[n]['workspace_path']).read_text();declared=re.findall(r'^#print axioms ([A-Za-z_][A-Za-z0-9_.\']*)\s*$',text,re.M)
 assert [x if x.startswith('DiophantineConsistency.') else n+'.'+x for x in declared]==reports[n]
spec={'status':'FROZEN_ADDITIONS','source_commit':a.source_commit,'order':names,'sources':sources,'axiom_reports':reports,
 'parent_manifest_sha256':base['parent_manifest_sha256'],
 'scope':'Joint single-overlay historical AQ29 author extension for 13-variable sum-square and product endpoints; not paired or current-source.'}
raw=(json.dumps(spec,indent=2,sort_keys=True)+'\n').encode();out=D/'author-additions.json'
if out.exists():assert out.read_bytes()==raw
else:out.write_bytes(raw)
print('FRONTIER13_FROZEN_MANIFEST',hashlib.sha256(raw).hexdigest())
