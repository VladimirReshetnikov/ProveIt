#!/usr/bin/env python3
"""Tiny Git-backed source-freezer controls; does not authenticate project objects."""
if not __debug__:
    raise RuntimeError('controls require Python assertions enabled')

from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch
import freeze

def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def command(root,*args):return subprocess.check_output(['git','-C',str(root),*args],text=True).strip()

with tempfile.TemporaryDirectory(prefix='reference-freeze-control-') as td:
    base=Path(td);root=base/'workspace';root.mkdir();command(root,'init','-q')
    (root/'lakefile.toml').write_text('name = "Toy"\n[[lean_lib]]\nname = "Toy"\nsrcDir = "src"\n')
    (root/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    policy=root/freeze.prepare.POLICY_REL;policy.parent.mkdir(parents=True)
    # Policy is written after its pinned source is created.
    src=root/'src/Toy';src.mkdir(parents=True)
    (src/'A.lean').write_text('prelude\n');(src/'New.lean').write_text('import Toy.A\n')
    policy.write_text(json.dumps({'target':'Toy.New','addition_order':['Toy.New'], 'sources':{'Toy.New':{'workspace_path':'src/Toy/New.lean','sha256':H(src/'New.lean'),'imports':['Toy.A']}}, 'expected_axiom_names':list(freeze.EXPECTED),'expected_axiom_by_module':{'Toy.New':list(freeze.EXPECTED)}}))
    freeze.prepare.POLICY_SHA256=H(policy)  # fixture-specific trust anchor
    command(root,'add','.');command(root,'-c','user.name=Toy','-c','user.email=toy@example.invalid','commit','-qm','source')
    snap=base/'parent';(snap/'src/Toy').mkdir(parents=True)
    (snap/'src/Toy/A.lean').write_bytes((src/'A.lean').read_bytes())
    old={'status':'FROZEN_NOT_COMPILED','root':str(root),'head':command(root,'rev-parse','HEAD'),'target':'Toy.A','order':['Toy.A'],
         'project_modules':1,'sources':{'Toy.A':{'workspace_path':'src/Toy/A.lean',
         'snapshot_path':'src/Toy/A.lean','sha256':H(src/'A.lean'),'imports':[]}},
         'lakefile_sha256':H(root/'lakefile.toml'),'lean_toolchain_sha256':H(root/'lean-toolchain'),
         'external_modules':[]}
    (snap/'manifest.json').write_text(json.dumps(old));real=freeze.load_planner()
    fake=SimpleNamespace(ROOT=root,TARGETS=('Toy.New',),draft_map=lambda root:{},plan=real.plan)
    actual=real.plan(root,snap,old,{'Toy':root/'src'},fake.TARGETS,{},'historical')
    actual.update({'parent_manifest_sha256':H(snap/'manifest.json'),'parent_snapshot':str(snap),
                   'planner_sha256':H(freeze.PLANNER),'workspace_head':old['head'],'additional_untracked':[],
                   'additional_modified_against_head':[]})
    plan=base/'strict.json';plan.write_text(json.dumps(actual));out=base/'output'
    parent=base/'pair';parent.mkdir();pair=parent/'pair-state.json'
    provider=base/'provider';provider.mkdir();receipt=provider/'receipt.json';receipt.write_text(json.dumps({'root':str(provider)}))
    package=provider/'package';package.mkdir();toolchain=base/'toolchain/bin';toolchain.mkdir(parents=True)
    lean=toolchain/'lean';lean.write_text('toy')
    (parent/'author').mkdir();(parent/'author/state.json').write_text(json.dumps({
        'provider':str(receipt),'provider_receipt_sha256':H(receipt),
        'package_overlay':str(package),'lean_path':str(lean)}))
    (parent/'peer').mkdir();(parent/'peer/state.json').write_text('{}')
    pair.write_text(json.dumps({'status':'MATCHED_PASS','snapshot_sha256':H(snap/'manifest.json'),
        'runs':[{'label':'author','exit':0,'builder_state_sha256':H(parent/'author/state.json')},
                {'label':'peer','exit':0,'builder_state_sha256':H(parent/'peer/state.json')}]}))
    observation=base/'observation.json';observation.write_text(json.dumps({'observed_exit_code':0,
        'observed_stdout':'MATCHED_PASS 1 rows\n','pair_state_sha256':H(pair),'pair_state_path':str(pair)}))
    args=['freeze.py','--old-snapshot',str(snap),'--old-sha256',H(snap/'manifest.json'),
          '--strict-plan',str(plan),'--strict-plan-sha256',H(plan),'--parent',str(parent),
          '--parent-pair-sha256',H(pair),'--parent-observation',str(observation),
          '--parent-observation-sha256',H(observation),'--output',str(out)]
    with patch.object(freeze,'load_planner',return_value=fake),patch.object(sys,'argv',args),redirect_stdout(io.StringIO()):freeze.run()
    result=json.loads((out/'manifest.json').read_text())
    assert result['order']==['Toy.A','Toy.New'] and result['target']=='Toy.New'
    assert result['expected_axiom_names']==list(freeze.EXPECTED)
    assert (out/'src/Toy/A.lean').read_bytes()==(snap/'src/Toy/A.lean').read_bytes()
    assert (out/'src/Toy/New.lean').read_bytes()==(src/'New.lean').read_bytes()
    assert result['status']=='FROZEN_NOT_COMPILED' and result['source_basis']=='HISTORICAL_PARENT'
    # A committed current-source change is allowed only on the parent side;
    # the new snapshot must still contain the exact original parent bytes.
    (src/'A.lean').write_text('prelude\n-- drift\n');command(root,'add','.')
    command(root,'-c','user.name=Toy','-c','user.email=toy@example.invalid','commit','-qm','parent drift')
    actual=real.plan(root,snap,old,{'Toy':root/'src'},fake.TARGETS,{},'historical')
    assert actual['parent_source_drift']==['Toy.A']
    actual.update({'parent_manifest_sha256':H(snap/'manifest.json'),'parent_snapshot':str(snap),
                   'planner_sha256':H(freeze.PLANNER),'workspace_head':command(root,'rev-parse','HEAD'),
                   'additional_untracked':[],'additional_modified_against_head':[]})
    plan.write_text(json.dumps(actual));args[args.index('--strict-plan-sha256')+1]=H(plan)
    args[-1]=str(base/'drift')
    with patch.object(freeze,'load_planner',return_value=fake),patch.object(sys,'argv',args),redirect_stdout(io.StringIO()):freeze.run()
    drift=json.loads((base/'drift/manifest.json').read_text())
    assert drift['source_basis']=='HISTORICAL_PARENT' and drift['parent_source_drift']==['Toy.A']
    assert (base/'drift/src/Toy/A.lean').read_bytes()==(snap/'src/Toy/A.lean').read_bytes()
    # Provisional plans cannot become authenticated source snapshots.
    actual['status']='PROVISIONAL_MANIFEST_PLAN';plan.write_text(json.dumps(actual));args[args.index('--strict-plan-sha256')+1]=H(plan)
    try:
        with patch.object(freeze,'load_planner',return_value=fake),patch.object(sys,'argv',args),redirect_stdout(io.StringIO()):freeze.run()
    except ValueError as e:assert 'strict historical-parent source plan required' in str(e),str(e)
    else:raise AssertionError('provisional plan accepted')
    actual['status']='SOURCE_PLAN_ONLY';plan.write_text(json.dumps(actual));args[args.index('--strict-plan-sha256')+1]=H(plan)
    bad=json.loads(observation.read_text());bad['observed_exit_code']=None;observation.write_text(json.dumps(bad))
    args[args.index('--parent-observation-sha256')+1]=H(observation)
    try:
        with patch.object(freeze,'load_planner',return_value=fake),patch.object(sys,'argv',args),redirect_stdout(io.StringIO()):freeze.run()
    except ValueError as e:assert 'parent coordinator terminal observation' in str(e),str(e)
    else:raise AssertionError('unobserved parent completion accepted')
    observation.write_text(json.dumps({'observed_exit_code':0,'observed_stdout':'MATCHED_PASS 1 rows\n',
        'pair_state_sha256':H(pair),'pair_state_path':str(pair)}))
    args[args.index('--parent-observation-sha256')+1]=H(observation)
    def reject_mutation(path,contents,reason):
        saved=path.read_bytes();path.write_bytes(contents)
        try:
            with patch.object(freeze,'load_planner',return_value=fake),patch.object(sys,'argv',args),redirect_stdout(io.StringIO()):freeze.run()
        except ValueError as e:assert reason in str(e),str(e)
        else:raise AssertionError(('invalid mutation accepted',reason))
        finally:path.write_bytes(saved)
    reject_mutation(parent/'author/state.json',b'{}','parent state changed')
    reject_mutation(receipt,b'{}','parent provider receipt changed')
    reject_mutation(policy,b'{}','task-specific target policy mismatch')
print('PASS: Git-backed freeze, source/policy/parent/provider drift and incomplete evidence rejected')
