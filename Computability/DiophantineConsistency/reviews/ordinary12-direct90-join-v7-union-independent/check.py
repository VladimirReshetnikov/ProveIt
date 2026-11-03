#!/usr/bin/env python3
"""Audit the retained v6 failure and simulate v7's union without Lean."""
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-direct90-ipra-join';A=H/'observations/attempt01';S=H/'run-v7.py'
PINS={S:'4fd1c8ea506edeb5e468b59a7367efd7e759681a70a283f1c30d0278774ec79c',
 A/'result.json':'ab5030de91271a6ecb9fd617ff214358adff69718828fdfec9dcc682dc308371',
 A/'stage-01.stdout':'05330977a4091966817e8f1c0a600d07518c751640be937254f9d7283161e1ea',
 A/'stage-01.json':'51df0aad3211d340a12117cd5ef1e4fb1ae47a39ffa6e7fedf307fd7cc127907'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
spec=importlib.util.spec_from_file_location('v7_review',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
failure=json.loads((A/'result.json').read_text());stage=json.loads((A/'stage-01.json').read_text())
need(failure['status']=='FAILED' and failure['stages']==[] and stage['exit']==1,'failure receipt')
name='DiophantineConsistency.IPRAOpenDisjunctionWitness';old=failure['pre_headers']['project'][name]
need(old['record']['sha256']=='5f139f9dde89d15c185fcfbc71252369bb11657b5f88ef81dcde7bec95b0fabf','pre-scan object')
need('object file' in (A/'stage-01.stdout').read_text() and name in (A/'stage-01.stdout').read_text(),'missing namespace diagnostic')
f=json.loads(m.FINAL.read_text());m.validate_final(f);m.manifest_recheck(f);before=m.snapshot_lib();g=failure['pre_headers']['project']
with tempfile.TemporaryDirectory(prefix='direct90-union-review-') as temp:
 out=Path(temp)/'lib';out.mkdir()
 for rel,record in before.items():
  dst=out/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  need(not os.path.lexists(dst),'canonical duplicate '+rel);os.symlink(record['resolved'],dst)
 for n in f['report']['direct_missing']:
  dst=out/n.replace('.','/');dst.parent.mkdir(parents=True,exist_ok=True)
  for suffix,record in f['records'][n]['selected_provider']['companions'].items():
   if record is not None:
    q=Path(str(dst)+suffix);need(not os.path.lexists(q),'supplemental collision '+n+suffix);os.symlink(record['resolved'],q)
 for n,row in g.items():
  stem=str(out/n.replace('.','/'))
  for suffix,expected in row['companions'].items():
   actual=m.rec(stem+suffix)
   need((None if expected is None else expected['sha256'])==(None if actual is None else actual['sha256']),
        'union dependency/companion mismatch '+n+suffix)
 dirs={x.name for x in out.iterdir() if x.is_dir()};package={x.name for x in m.PACKAGE.iterdir() if x.is_dir()}
 need(not dirs&package,'project/package namespace overlap')
 union={x.relative_to(out).as_posix():m.rec(x) for x in out.rglob('*') if x.is_file()}
 need(len(union)==2681 and len(g)==1605,'unexpected union or closure size')
 adapter=json.loads(m.ADAPTER.read_text());order=adapter['rebuild_order'];need([x['module'] for x in order]==m.AFFECTED,'affected order')
 for i,row in enumerate(order):
  need(all(dep not in m.AFFECTED or m.AFFECTED.index(dep)<i for dep in row['serialized_imports']), 'stale affected direct import')
  need(sha(m.ROOT/row['source'])==row['source_sha256'],'affected source changed')
 removed=0
 for n in m.AFFECTED:
  for suffix in m.SUFFIXES:
   q=Path(str(out/n.replace('.','/'))+suffix)
   if os.path.lexists(q):
    need(q.is_symlink(),'unsafe affected output '+str(q));q.unlink();removed+=1
 need(removed==4 and m.snapshot_lib()==before,'unexpected replacement/canonical drift')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
print(json.dumps({'status':'PASS','v7_sha256':PINS[S],'v6_stage01_exit':1,'union_files':len(union),
 'pre_project_modules':len(g),'affected_symlinks_removed':removed,'package_namespace_overlap':[],
 'canonical_unchanged':True,'scope':'independent temporary union simulation; no Lean launch or join'},indent=2,sort_keys=True))
