#!/usr/bin/env python3
"""Freeze a strict historical-parent extension; not parent-object authentication.

Run only after the active parent pair completes. This copies every frozen
parent source, plus the exact additional source closure, to a new root.
Actual pair authentication and sibling-specific seed copying are performed by
prepare.py, not by this source freezer.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tomllib
import prepare

HERE=Path(__file__).resolve().parent
PLANNER=HERE.parent/'paired_plan.py'
EXPECTED=(
    'DiophantineConsistency.IPRASquareWitnessDirect14Native.sameZero13',
    'DiophantineConsistency.IPRASquareWitnessDirect14Native.bridge13',
    'DiophantineConsistency.IPRASquareWitnessDirect14Native.sameNoZero14',
    'DiophantineConsistency.IPRASquareWitnessDirect14Native.bridge14',
    'DiophantineConsistency.IPRASquareWitnessDirect14Native.literal_equivalence',
    'DiophantineConsistency.IPRAStandardDirect14.literal_equivalence',
    'DiophantineConsistency.IPRAStandardDirect14.selected_foundation_consistency',
    'DiophantineConsistency.IPRAStandardDirect14.literal_iff_translated_consistency',
)
H=prepare.digest

def load_planner():
    spec=importlib.util.spec_from_file_location('reference_replay_plan',PLANNER)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def reject_workspace_symlinks(root,manifest):
    for row in manifest['sources'].values():
        rel=Path(row['workspace_path'])
        if rel.is_absolute() or '..' in rel.parts or not rel.parts:
            raise ValueError(('workspace path escapes root',str(rel)))
        cur=root
        for part in rel.parts:
            cur=cur/part
            if cur.is_symlink():raise ValueError(('workspace source symlink',str(cur)))

def run():
    p=argparse.ArgumentParser();p.add_argument('--old-snapshot',type=Path,required=True)
    p.add_argument('--old-sha256',required=True);p.add_argument('--strict-plan',type=Path,required=True)
    p.add_argument('--strict-plan-sha256',required=True);p.add_argument('--parent',type=Path,required=True)
    p.add_argument('--parent-pair-sha256',required=True);p.add_argument('--parent-observation',type=Path,required=True)
    p.add_argument('--parent-observation-sha256',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();old_snap=a.old_snapshot.resolve(strict=True);old_path=old_snap/'manifest.json'
    if H(old_path)!=a.old_sha256 or H(a.strict_plan)!=a.strict_plan_sha256:raise ValueError('input pin mismatch')
    old=json.loads(old_path.read_text());record=json.loads(a.strict_plan.read_text());planner=load_planner()
    parent=a.parent.resolve(strict=True);pair_path=parent/'pair-state.json';observation=a.parent_observation.resolve(strict=True)
    if H(pair_path)!=a.parent_pair_sha256 or H(observation)!=a.parent_observation_sha256:
        raise ValueError('parent completion evidence pin mismatch')
    pair=json.loads(pair_path.read_text())
    prepare.check_parent_observation(json.loads(observation.read_text()),a.parent_pair_sha256,pair_path,len(old['order']))
    if (pair['status']!='MATCHED_PASS' or pair['snapshot_sha256']!=a.old_sha256 or
            [(r['label'],r['exit']) for r in pair['runs']]!=[('author',0),('peer',0)]):
        raise ValueError('completed matched parent required')
    for row in pair['runs']:
        if H(parent/row['label']/'state.json')!=row['builder_state_sha256']:
            raise ValueError(('parent state changed',row['label']))
    parent_state=json.loads((parent/'author/state.json').read_text())
    provider=Path(parent_state['provider']).resolve(strict=True)
    if H(provider)!=parent_state['provider_receipt_sha256']:
        raise ValueError('parent provider receipt changed')
    provider_root=Path(json.loads(provider.read_text())['root']).resolve(strict=True)
    package=Path(parent_state['package_overlay']).resolve(strict=True)
    toolchain=Path(parent_state['lean_path']).resolve(strict=True).parent.parent
    tool_hashes={'freezer_sha256':H(Path(__file__)),'preparer_sha256':H(Path(prepare.__file__)),
                 'planner_sha256':H(PLANNER)}
    if (record['status']!='SOURCE_PLAN_ONLY' or record['basis']!='historical' or not isinstance(record['parent_source_drift'],list)
            or record['parent_manifest_sha256']!=a.old_sha256 or record['parent_snapshot']!=str(old_snap)
            or record['planner_sha256']!=H(PLANNER) or record['targets']!=list(planner.TARGETS)
            or record['additional_untracked'] or record['additional_modified_against_head']):
        raise ValueError('strict historical-parent source plan required')
    root=Path(old['root']).resolve(strict=True)
    if root!=planner.ROOT.resolve():raise ValueError('workspace mismatch')
    prepare.verify_snapshot(old_snap,old,False);reject_workspace_symlinks(root,old)
    before=prepare.verify_current_git(old)
    if record['workspace_head']!=before:raise ValueError('planned source commit changed')
    cfg=tomllib.loads((root/'lakefile.toml').read_text())
    libs={x['name']:root/x.get('srcDir','.') for x in cfg['lean_lib']};libs.pop('Foundation',None)
    drafts=planner.draft_map(root)
    actual=planner.plan(root,old_snap,old,libs,planner.TARGETS,drafts,'historical')
    for key in ('status','basis','targets','parent_source_modules_used','additional_project_modules',
                'parent_source_drift','order','sources','external_modules'):
        if actual[key]!=record[key]:raise ValueError(('source plan drift',key))
    names=actual['additional_project_modules']
    if names!=list(planner.TARGETS):raise ValueError('incomplete or reordered direct14 additions')
    rows={n:dict(old['sources'][n]) for n in old['order']}
    for name in names:
        row=actual['sources'][name]
        rows[name]={'workspace_path':row['workspace_path'],'snapshot_path':'src/'+name.replace('.','/')+'.lean',
                    'sha256':row['source_sha256'],'imports':row['imports']}
    policy=root/prepare.POLICY_REL
    task=json.loads(policy.read_text())
    if (task.get('target')!=planner.TARGETS[-1] or task.get('addition_order')!=names or
        task.get('expected_axiom_names')!=list(EXPECTED)):
        raise ValueError('task-specific target policy mismatch')
    new={'status':'FROZEN_NOT_COMPILED','target':planner.TARGETS[-1],'root':str(root),
         'head':before,'lakefile_sha256':old['lakefile_sha256'],'lean_toolchain_sha256':old['lean_toolchain_sha256'],
         'project_modules':len(rows),'order':old['order']+names,'sources':rows,
         'external_modules':sorted(set(old['external_modules'])|set(actual['external_modules'])),
         'expected_axiom_names':list(EXPECTED),'expected_axiom_by_module':task['expected_axiom_by_module'],
         'parent_manifest_sha256':a.old_sha256,
         'source_basis':'HISTORICAL_PARENT','parent_git_commit':old['head'],
         'parent_source_count':len(old['order']),'parent_source_drift':record['parent_source_drift'],
         'strict_plan_sha256':a.strict_plan_sha256,'target_policy_sha256':H(policy),
         'parent_pair_sha256':a.parent_pair_sha256,'parent_observation_sha256':a.parent_observation_sha256,
         **tool_hashes,
         'scope':'Historical parent sources plus separately committed additions; parent objects and proof replay are not authenticated here.'}
    prepare.validate_graph(new);prepare.verify_policy(new);reject_workspace_symlinks(root,new)
    output=a.output.absolute()
    if output.exists() or output.is_symlink():raise ValueError('refusing to overwrite snapshot')
    for protected in (old_snap,root,parent,observation,a.strict_plan.resolve(strict=True),
                      provider_root,package,toolchain):
        if output.resolve().is_relative_to(protected) or protected.is_relative_to(output.resolve()):
            raise ValueError(('snapshot overlaps protected root',str(protected)))
    if not output.parent.is_dir():raise ValueError('snapshot parent directory must already exist')
    size=sum(((old_snap/rows[n]['snapshot_path']) if n in old['sources'] else
              (root/rows[n]['workspace_path'])).stat().st_size for n in new['order'])
    if shutil.disk_usage(output.parent).free < size+prepare.MIN_FREE:
        raise ValueError('insufficient disk for frozen sources and reserve')
    output.mkdir(parents=True)
    try:
        for name in new['order']:
            if shutil.disk_usage(output).free < prepare.MIN_FREE:raise ValueError('disk reserve exhausted during source freeze')
            row=rows[name];src=(old_snap/row['snapshot_path']) if name in old['sources'] else (root/row['workspace_path'])
            dst=output/row['snapshot_path'];dst.parent.mkdir(parents=True,exist_ok=True)
            with src.open('rb') as f, dst.open('xb') as g:shutil.copyfileobj(f,g)
            if H(dst)!=row['sha256'] or H(src)!=row['sha256']:raise ValueError(('source drift during copy',name))
        prepare.verify_historical_sources(old_snap,old,output,new);after=prepare.verify_current_git(new)
        if after!=before:raise ValueError('workspace commit changed during freeze')
        if (H(old_path)!=a.old_sha256 or H(a.strict_plan)!=a.strict_plan_sha256 or
                H(pair_path)!=a.parent_pair_sha256 or H(observation)!=a.parent_observation_sha256 or
                H(provider)!=parent_state['provider_receipt_sha256'] or
                H(PLANNER)!=tool_hashes['planner_sha256'] or H(Path(__file__))!=tool_hashes['freezer_sha256'] or
                H(Path(prepare.__file__))!=tool_hashes['preparer_sha256']):
            raise ValueError('pinned source input changed')
        for row in pair['runs']:
            if H(parent/row['label']/'state.json')!=row['builder_state_sha256']:
                raise ValueError(('parent state changed during freeze',row['label']))
        new['head_after']=after
        (output/'manifest.json').write_text(json.dumps(new,indent=2,sort_keys=True)+'\n')
        print('FROZEN_NOT_COMPILED',len(new['order']),'sources',H(output/'manifest.json'),flush=True)
    except BaseException as exc:
        (output/'failure.txt').write_text(repr(exc)+'\n');raise

if __name__=='__main__':run()
