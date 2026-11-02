#!/usr/bin/env python3
"""End-to-end tiny Lean parent -> observed freezer -> paired extension control.

The task names below are toy theorems, not the real reference endpoint. This
test must never read or modify the real AQ29 snapshot or live pair.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL=LEAN.parent.parent/'lib/lean'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def run(*args,cwd=None):
    q=subprocess.run(list(map(str,args)),cwd=cwd,capture_output=True,text=True)
    if q.returncode:raise RuntimeError((args,q.returncode,q.stdout,q.stderr))
    return q

with tempfile.TemporaryDirectory(prefix='reference-full-chain-control-') as td:
    base=Path(td);workspace=base/'workspace';workspace.mkdir()
    run('git','init','-q',cwd=workspace)
    research=workspace/'Computability/DiophantineConsistency/research'
    parent_tools=research/'fresh-project-closure';parent_tools.mkdir(parents=True)
    for name in ('rebuild.py','compare.py','run_pair.py'):
        shutil.copyfile(RESEARCH/'fresh-project-closure'/name,parent_tools/name)
    plan_dir=research/'ipra-standard-aq29';ext=plan_dir/'extension';ext.mkdir(parents=True)
    shutil.copyfile(RESEARCH/'ipra-standard-aq29/plan.py',plan_dir/'plan.py')
    for name in ('freeze.py','prepare.py','rebuild.py','compare.py','run_pair.py','task-policy.json'):
        shutil.copyfile(HERE/name,ext/name)
    (workspace/'lakefile.toml').write_text('name = "Toy"\n[[lean_lib]]\nname = "DiophantineConsistency"\nsrcDir = "ToyLean"\n')
    (workspace/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    src=workspace/'ToyLean/DiophantineConsistency';src.mkdir(parents=True)
    (src/'Base.lean').write_text('def value : Nat := 1\n')
    (src/'ParentChecks.lean').write_text('import DiophantineConsistency.Base\ntheorem parentToy : value = 1 := rfl\n#print axioms parentToy\n')
    draft=research/'ipra-standard-aq29/draft';draft.mkdir(parents=True)
    target=draft/'IPRAStandardAQ29Checks.lean'
    names=[
      'DiophantineConsistency.IPRAStandardTheory.provable_iff',
      'DiophantineConsistency.IPRAStandardAQ29.literal_equivalence',
      'DiophantineConsistency.IPRAStandardAQ29.selected_foundation_consistency',
      'DiophantineConsistency.IPRAStandardAQ29.literal_iff_translated_consistency',
    ]
    definitions='\n'.join('namespace '+n.rsplit('.',1)[0]+'\ntheorem '+n.rsplit('.',1)[1]+' : True := trivial\nend '+n.rsplit('.',1)[0] for n in names)
    target.write_text('import DiophantineConsistency.ParentChecks\n'+definitions+'\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
    run('git','add','.',cwd=workspace)
    run('git','-c','user.name=Toy','-c','user.email=toy@example.invalid','commit','-qm','toy full chain',cwd=workspace)
    old=base/'old';rows={};modules=['DiophantineConsistency.Base','DiophantineConsistency.ParentChecks']
    for name in modules:
        rel=name.replace('.','/')+'.lean';q=old/'src'/rel;q.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(workspace/'ToyLean'/rel,q)
        rows[name]={'workspace_path':'ToyLean/'+rel,'snapshot_path':'src/'+rel,'sha256':H(q),
                    'imports':[] if name.endswith('.Base') else [modules[0]]}
    old_manifest={'status':'FROZEN_NOT_COMPILED','root':str(workspace),'target':modules[-1],
      'order':modules,'project_modules':len(modules),'sources':rows,'external_modules':[],
      'lakefile_sha256':H(workspace/'lakefile.toml'),'lean_toolchain_sha256':H(workspace/'lean-toolchain')}
    (old/'manifest.json').write_text(json.dumps(old_manifest))
    provider=base/'provider';foundation=provider/'.lake/build/lib/lean/Foundation';foundation.mkdir(parents=True)
    pkg=provider/'package-lib';pkg.mkdir();(pkg/'Foundation').symlink_to(foundation)
    for name in ('Init','Init.olean','Init.ir','Init.olean.private','Init.olean.server'):
        q=TOOL/name
        if q.exists():(pkg/name).symlink_to(q,target_is_directory=q.is_dir())
    finput=provider/'input.json';finput.write_text(json.dumps({'lean_sha256':H(LEAN)}))
    provider_receipt=provider/'receipt.json';provider_receipt.write_text(json.dumps({
      'manifest_sha256':H(finput),'status':'BUILT','exit_code':0,'declared_external_guard':{},
      'overlay':str(pkg),'root':str(provider),'foundation_artifacts':{}}))
    parent=base/'parent'
    q=run(sys.executable,parent_tools/'run_pair.py','--snapshot',old,'--snapshot-sha256',H(old/'manifest.json'),
      '--provider-receipt',provider_receipt,'--provider-sha256',H(provider_receipt),'--foundation-input',finput,
      '--expected-axiom-reports','1','--output',parent)
    pair=parent/'pair-state.json';parent_obs=base/'parent-observation.json'
    parent_obs.write_text(json.dumps({'observed_exit_code':q.returncode,'observed_stdout':q.stdout,
      'pair_state_sha256':H(pair),'pair_state_path':str(pair)}))
    plan=base/'strict-plan.json'
    run(sys.executable,plan_dir/'plan.py','--snapshot',old,'--parent-sha256',H(old/'manifest.json'),
      '--basis','current','--output',plan)
    assert json.loads(plan.read_text())['additional_project_modules']==['DiophantineConsistency.IPRAStandardAQ29Checks']
    new=base/'new'
    q=run(sys.executable,ext/'freeze.py','--old-snapshot',old,'--old-sha256',H(old/'manifest.json'),
      '--strict-plan',plan,'--strict-plan-sha256',H(plan),'--parent',parent,'--parent-pair-sha256',H(pair),
      '--parent-observation',parent_obs,'--parent-observation-sha256',H(parent_obs),'--output',new)
    freezer_obs=base/'freezer-observation.json'
    freezer_obs.write_text(json.dumps({'observed_exit_code':q.returncode,'observed_stdout':q.stdout,
      'snapshot_manifest_sha256':H(new/'manifest.json'),'snapshot_path':str(new)}))
    prepared=base/'prepared'
    run(sys.executable,ext/'prepare.py','--parent',parent,'--old-snapshot',old,'--new-snapshot',new,
      '--old-sha256',H(old/'manifest.json'),'--new-sha256',H(new/'manifest.json'),
      '--parent-pair-sha256',H(pair),'--parent-observation',parent_obs,
      '--parent-observation-sha256',H(parent_obs),'--freezer-observation',freezer_obs,
      '--freezer-observation-sha256',H(freezer_obs),'--output',prepared)
    extension_pair=base/'extension-pair'
    q=run(sys.executable,ext/'run_pair.py','--prepared',prepared,'--preparation-sha256',H(prepared/'preparation.json'),
      '--old-snapshot',old,'--new-snapshot',new,'--expected-axiom-reports',str(len(names)),'--output',extension_pair)
    pair_state=json.loads((extension_pair/'pair-state.json').read_text())
    assert q.returncode==0 and pair_state['status']=='MATCHED_SELECTIVE_PASS'
    assert [r['exit'] for r in pair_state['runs']]==[0,0]
    assert pair_state['comparison']['affected_modules']==1
    for label in ('author','peer'):
        state=json.loads((prepared/label/'rebuild-state.json').read_text())
        assert state['records'][-1]['axiom_report_names']==names
print('PASS: actual observed toy parent, freezer, preparation and paired extension; no AQ29 proof')
