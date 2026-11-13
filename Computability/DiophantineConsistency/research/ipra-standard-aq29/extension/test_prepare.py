#!/usr/bin/env python3
"""Pure controls for strict source-extension selection and report names."""
import copy
import unittest
import prepare

def graphs():
    old={'order':['P.A','P.B'],'target':'P.B','project_modules':2,
         'sources':{'P.A':{'sha256':'a','imports':[],'workspace_path':'A.lean'},
                    'P.B':{'sha256':'b','imports':['P.A'],'workspace_path':'B.lean'}}}
    new=copy.deepcopy(old);new['order']+=['P.C','P.Check'];new['project_modules']=4;new['target']='P.Check'
    new['sources'].update({'P.C':{'sha256':'c','imports':['P.A'],'workspace_path':'C.lean'},
                           'P.Check':{'sha256':'d','imports':['P.B','P.C'],'workspace_path':'Check.lean'}})
    new['expected_axiom_names']=['P.result']
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
            'planner_sha256':prepare.HERE.parent/'plan.py'}.items()}
        prepare.verify_freezer_identity(good)
        for key in good:
            with self.assertRaisesRegex(ValueError,'freezer tool provenance mismatch'):
                prepare.verify_freezer_identity(dict(good,**{key:'wrong'}))

if __name__=='__main__':unittest.main()
