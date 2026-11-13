#!/usr/bin/env python3
"""Plan, but do not compile, a 14-variable standard-iPRA author extension."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tomllib

D=Path(__file__).resolve().parent
ROOT=D.parents[3]
PARENT=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PARENT_SHA='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
PLANNER=ROOT/'Computability/DiophantineConsistency/research/ipra-standard-aq29/plan.py'
TARGET='DiophantineConsistency.IPRAStandardCurrentEndpointChecks'
OUTPUT=D/'author-additions.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=(PARENT/'manifest.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!=PARENT_SHA: raise ValueError('parent manifest pin differs')
parent=json.loads(raw)
spec=importlib.util.spec_from_file_location('standard_plan',PLANNER)
planner=importlib.util.module_from_spec(spec);spec.loader.exec_module(planner)
cfg=tomllib.loads((ROOT/'lakefile.toml').read_text())
libs={x['name']:ROOT/x.get('srcDir','.') for x in cfg['lean_lib']};libs.pop('Foundation',None)
result=planner.plan(ROOT,PARENT,parent,libs,[TARGET],{},'historical',True)
old_externals={dep for row in parent['sources'].values() for dep in row['imports'] if dep.split('.')[0] not in libs}
new_externals=sorted(set(result['external_modules'])-old_externals)
if new_externals: raise ValueError(('new declared external imports',new_externals))
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
order=result['additional_project_modules'];sources={}
for name in order:
    row=result['sources'][name];rel=row['workspace_path'];path=ROOT/rel
    entry=subprocess.check_output(['git','ls-tree','-z',head,'--',rel],cwd=ROOT)
    meta,sep,tree_path=entry.partition(b'\t')
    if not sep or tree_path!=rel.encode()+b'\0' or meta.split(b' ')[:2] not in ([b'100644',b'blob'],[b'100755',b'blob']):
        raise ValueError(('not a regular Git blob',name))
    blob=subprocess.check_output(['git','show',head+':'+rel],cwd=ROOT)
    sha=hashlib.sha256(blob).hexdigest()
    if path.is_symlink() or H(path)!=sha or sha!=row['source_sha256']:
        raise ValueError(('addition source drift',name))
    sources[name]={'workspace_path':rel,'sha256':sha,'imports':row['imports']}
checks=(ROOT/sources[TARGET]['workspace_path']).read_text().splitlines()
reports=[line.split(maxsplit=2)[2] for line in checks if line.startswith('#print axioms ')]
expected=['DiophantineConsistency.IPRAStandardTheory.leibniz',
          'DiophantineConsistency.IPRAStandardTheory.provable_iff',
          'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency',
          'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency']
if reports!=expected: raise ValueError(('diagnostic names differ',reports))
for name in order:
    if name!=TARGET and any(line.lstrip().startswith('#print axioms ') for line in (ROOT/sources[name]['workspace_path']).read_text().splitlines()):
        raise ValueError(('unrecorded diagnostic',name))
if subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()!=head:
    raise ValueError('Git HEAD changed during survey')
out={'status':'FROZEN_ADDITIONS','source_commit':head,'order':order,'sources':sources,
     'axiom_reports':{TARGET:expected},'parent_manifest_sha256':PARENT_SHA,
     'parent_modules_used':len(result['parent_source_modules_used']),
     'direct_external_not_in_parent':new_externals,
     'planner_sha256':H(PLANNER),'survey_sha256':H(Path(__file__)),
     'scope':'Provisional source-declared graph; parent bytes/drift and Lean parsing unchecked. No compilation or proof claimed.'}
if OUTPUT.exists() or OUTPUT.is_symlink(): raise ValueError('refusing to overwrite manifest')
OUTPUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('FROZEN_ADDITIONS',len(order),'parent_modules',out['parent_modules_used'],H(OUTPUT))
