#!/usr/bin/env python3
"""Pure controls for strict source-extension selection and report names."""
if not __debug__:
    raise RuntimeError('controls require Python assertions enabled')

import copy
import json
import tempfile
from pathlib import Path
import unittest
import prepare

def graphs():
    old={'order':['P.A','P.B'],'target':'P.B','project_modules':2,
         'sources':{'P.A':{'sha256':'a','imports':[],'workspace_path':'A.lean'},
                    'P.B':{'sha256':'b','imports':['P.A'],'workspace_path':'B.lean'}}}
    new=copy.deepcopy(old);new['order']+=['P.C','P.Check'];new['project_modules']=4;new['target']='P.Check'
    new['sources'].update({'P.C':{'sha256':'c','imports':['P.A'],'workspace_path':'C.lean'},
                           'P.Check':{'sha256':'d','imports':['P.B','P.C'],'workspace_path':'Check.lean'}})
    new['expected_axiom_names']=['P.result'];new['parent_source_count']=2
    new['expected_axiom_by_module']={'P.C':[],'P.Check':['P.result']}
    records=[{'module':'P.A','direct_inputs':{}},
             {'module':'P.B','direct_inputs':{'P.A':{'kind':'project'}}}]
    return old,new,records

class ExtensionTests(unittest.TestCase):
    def test_strict_extension(self):
        a,b,r=graphs();got=prepare.select(a,b,r)
        self.assertEqual(got['affected'],['P.C','P.Check'])
        self.assertEqual(got['unaffected'],a['order']);self.assertEqual(got['changed'],[])
    def test_old_source_or_import_drift(self):
        for key,val in (('sha256','bad'),('imports',[]),('workspace_path','bad')):
            a,b,r=graphs();b['sources']['P.B'][key]=val
            with self.assertRaisesRegex(ValueError,'parent source drift'):prepare.select(a,b,r)
    def test_parent_import_reclassified_as_new_project(self):
        a,b,r=graphs();a['sources']['P.A']['imports']=['P.C'];b['sources']['P.A']['imports']=['P.C']
        r[0]['direct_inputs']={'P.C':{'kind':'package'}}
        # Old A could have imported an external P.C; the new graph must not
        # reinterpret that old object as depending on the new project P.C.
        with self.assertRaisesRegex(ValueError,'non-topological project import|shadows parent dependency'):
            prepare.select(a,b,r)
    def test_external_shadow_even_when_old_manifest_omits_extra(self):
        a,b,r=graphs();r[0]['direct_inputs']={'Init':{'kind':'toolchain'}}
        b['order'].insert(2,'Init');b['project_modules']+=1
        b['sources']['Init']={'sha256':'i','imports':[],'workspace_path':'Init.lean'}
        b['expected_axiom_by_module']['Init']=[]
        with self.assertRaisesRegex(ValueError,'shadows parent dependency'):
            prepare.select(a,b,r)
    def test_old_omission_or_reordering(self):
        a,b,r=graphs();b['order']=['P.B','P.A','P.C','P.Check']
        with self.assertRaises(ValueError):prepare.select(a,b,r)
    def test_same_count_wrong_axiom_name_is_not_equivalent(self):
        _,b,_=graphs();self.assertEqual(prepare.expected_names(b),['P.result'])
        self.assertNotEqual(prepare.expected_names(b),['P.other'])
        for bad in ([],['P.x','P.x'],['P.bad/name']):
            b['expected_axiom_names']=bad
            with self.assertRaises(ValueError):prepare.expected_names(b)
    def test_policy_matches_independent_successful_manifest_and_has_all_reports(self):
        source=prepare.HERE.parent/'author-additions.json'
        self.assertEqual(prepare.digest(source),'1a04dbd22330a61cb2f134f6875513e9457190fca0da7127f500fe6098db1f8b')
        original=json.loads(source.read_text()); path=prepare.HERE/'task-policy.json'
        self.assertEqual(prepare.digest(path),prepare.POLICY_SHA256)
        policy=json.loads(path.read_text()); order=original['order']
        self.assertEqual(len(order),30);self.assertEqual(policy['addition_order'],order)
        self.assertEqual(policy['sources'],original['sources'])
        reports={name:original['axiom_reports'].get(name,[]) for name in order}
        self.assertEqual(policy['expected_axiom_by_module'],reports)
        self.assertEqual(sum(map(len,reports.values())),79)
        self.assertEqual(sum(bool(v) for v in reports.values()),22)
        self.assertEqual(policy['target'],order[-1])
        self.assertEqual(policy['expected_axiom_names'],reports[order[-1]])
    def test_self_consistent_modified_policy_and_manifest_rejected(self):
        real=json.loads((prepare.HERE/'task-policy.json').read_text())
        for mode in ('drop_module','drop_report'):
            policy=copy.deepcopy(real)
            name=next(n for n in policy['addition_order'][:-1] if policy['expected_axiom_by_module'][n])
            if mode=='drop_module':
                policy['addition_order'].remove(name);del policy['sources'][name]
                del policy['expected_axiom_by_module'][name]
            else: policy['expected_axiom_by_module'][name].pop()
            with tempfile.TemporaryDirectory() as td:
                path=Path(td)/prepare.POLICY_REL;path.parent.mkdir(parents=True)
                path.write_text(json.dumps(policy))
                manifest={'root':td,'target':policy['target'],'order':['P.Parent']+policy['addition_order'],
                  'parent_source_count':1,'sources':policy['sources'],
                  'expected_axiom_names':policy['expected_axiom_names'],
                  'expected_axiom_by_module':policy['expected_axiom_by_module'],
                  'target_policy_sha256':prepare.digest(path)}
                with self.assertRaisesRegex(ValueError,'extension target policy mismatch'):
                    prepare.verify_policy(manifest)
    def test_missing_or_invented_per_module_policy_is_rejected(self):
        for mutation in ('missing','extra','bad_target'):
            _,b,_=graphs()
            if mutation=='missing':del b['expected_axiom_by_module']['P.C']
            if mutation=='extra':b['expected_axiom_by_module']['P.Unknown']=[]
            if mutation=='bad_target':b['expected_axiom_by_module']['P.Check']=['P.other']
            with self.assertRaises(ValueError):prepare.expected_reports(b,'P.C')
    def test_parent_records_must_cover_direct_imports(self):
        a,b,r=graphs();r[1]['direct_inputs']={}
        with self.assertRaisesRegex(ValueError,'actual/declaration mismatch'):prepare.select(a,b,r)
    def test_freezer_observation_binds_exit_path_and_manifest(self):
        from pathlib import Path
        path=Path('/tmp/toy-snapshot');good={'observed_exit_code':0,
            'observed_stdout':'FROZEN_NOT_COMPILED 4 sources digest\n',
            'snapshot_manifest_sha256':'digest','snapshot_path':str(path)}
        prepare.check_freezer_observation(good,'digest',path,4)
        for bad in ({'observed_exit_code':None},{'snapshot_manifest_sha256':'other'},
                    {'snapshot_path':'/tmp/other'},{'observed_stdout':'FROZEN_NOT_COMPILED 3 sources digest\n'}):
            with self.assertRaisesRegex(ValueError,'freezer terminal observation'):
                prepare.check_freezer_observation(dict(good,**bad),'digest',path,4)
    def test_freezer_tools_are_pinned(self):
        good={key:prepare.digest(path) for key,path in {
            'freezer_sha256':prepare.HERE/'freeze.py','preparer_sha256':prepare.HERE/'prepare.py',
            'planner_sha256':prepare.HERE.parent/'paired_plan.py'}.items()}
        prepare.verify_freezer_identity(good)
        for key in good:
            with self.assertRaisesRegex(ValueError,'freezer tool provenance mismatch'):
                prepare.verify_freezer_identity(dict(good,**{key:'wrong'}))

if __name__=='__main__':unittest.main()
