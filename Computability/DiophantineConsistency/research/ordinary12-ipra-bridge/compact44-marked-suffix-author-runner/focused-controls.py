#!/usr/bin/env python3
"""No-Lean isolated controls of the actual runner helpers, not a full fake loop."""
import importlib.util,json,os,sys,tempfile
from pathlib import Path
P=Path(__file__).resolve().parent/'replay.py'
spec=importlib.util.spec_from_file_location('wang_runner',P);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def need(ok,msg):
 if not ok:raise ValueError(msg)
def rejected(fn):
 try:fn()
 except (ValueError,OSError):return True
 return False
need(__debug__ and not sys.flags.optimize,'optimized Python rejected')
results={}
with tempfile.TemporaryDirectory(prefix='wang-focused-controls-') as tmp:
 root=Path(tmp);lib=root/'lib';pkg=root/'pkg';lib.mkdir();pkg.mkdir()
 for x in (lib,pkg): (x/'Demo').mkdir()
 lp=lib/'Demo/Input.olean';pp=pkg/'Demo/Input.olean';pp.write_bytes(b'package')
 guards={};m.merge_guards(guards,m.slots(Path(str(lp)[:-6])));m.merge_guards(guards,m.slots(Path(str(pp)[:-6])))
 mapping={'Demo.Input':{'kind':'static','path':str(pp),'record':m.rec(pp)}}
 need(m.resolve_mapping(mapping,{},lib,pkg)=={str(pp.resolve())},'baseline mapping');m.check(guards);results['baseline_mapping']=True
 lp.write_bytes(b'shadow');results['reject_higher_priority_object']=rejected(lambda:m.check(guards)) and rejected(lambda:m.resolve_mapping(mapping,{},lib,pkg));lp.unlink()
 companion=Path(str(lp)+'.private');companion.write_bytes(b'new');results['reject_higher_priority_companion']=rejected(lambda:m.check(guards));companion.unlink()
 companion=Path(str(pp)+'.private');companion.write_bytes(b'new');results['reject_package_companion']=rejected(lambda:m.check(guards));companion.unlink()
 pp.write_bytes(b'changed');results['reject_package_byte_change']=rejected(lambda:m.check(guards)) and rejected(lambda:m.resolve_mapping(mapping,{},lib,pkg));pp.write_bytes(b'package')
 m.merge_guards(guards,m.slots(Path(str(pp)[:-6])));changed=dict(m.slots(Path(str(pp)[:-6])));changed[str(pp)]={'realpath':str(pp),'sha256':'different'}
 results['reject_inconsistent_repeat']=rejected(lambda:m.merge_guards(guards,changed))
 p=lib/'Demo/Produced.olean';p.write_bytes(b'output');produced={'Demo.Produced':m.rec(p)};mp={'Demo.Produced':{'kind':'produced','path':str(p)}}
 need(m.resolve_mapping(mp,produced,lib,pkg)=={str(p.resolve())},'produced mapping');p.write_bytes(b'changed');results['reject_changed_produced_object']=rejected(lambda:m.resolve_mapping(mp,produced,lib,pkg))
 inside=root/'inside';inside.mkdir();outside=root/'outside';outside.mkdir();(inside/'nested').symlink_to(outside,target_is_directory=True)
 results['reject_redirected_output_directory']=rejected(lambda:m.safe_dir(root,inside/'nested'))
source='#print axioms Demo.one\n';good="'Demo.one' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
results['accept_multiline_report']=m.report_inventory(source,good)=={'Demo.one':['propext','Classical.choice','Quot.sound']}
results['accept_recorded_smaller_set']=m.report_inventory(source,"'Demo.one' depends on axioms: [propext]\n")=={'Demo.one':['propext']}
results['accept_empty_module']=m.report_inventory('','')=={}
for name,out in [('missing_report',''),('wrong_name',"'Demo.two' depends on axioms: [propext]\n"),('unknown_axiom',"'Demo.one' depends on axioms: [Unexpected.axiom]\n"),('empty_set',"'Demo.one' depends on axioms: []\n"),('duplicate_report',good+good),('unexpected_output',good+'extra\n')]:
 results['reject_'+name]=rejected(lambda out=out:m.report_inventory(source,out))
need(all(results.values()),('failed control',results));print(json.dumps({'status':'PASS_NO_LEAN_FOCUSED_CONTROLS','scope':'isolated helpers only, not a full fake loop','cases':results},sort_keys=True))
