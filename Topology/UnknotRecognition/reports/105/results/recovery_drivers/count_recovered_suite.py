"""Inventory test IDs after baseline restoration; this never runs the suite."""
from pathlib import Path
from datetime import datetime,timezone
import json
import os
import sys
import unittest
HERE=Path(__file__).resolve().parent
FAST=HERE.parent/'ProveIt/Topology/UnknotRecognition/fast'
sys.path[:0]=[str(FAST/'tests'),str(FAST)]
os.chdir(FAST)
loader=unittest.TestLoader()
suite=loader.discover(str(FAST/'tests'))

def ids(s):
 if isinstance(s,unittest.TestSuite):
  return [name for child in s for name in ids(child)]
 return [s.id()]

all_ids=ids(suite)
path=HERE/'failed_module_recovery.json'
r=json.loads(path.read_text())
imports=[e['module'] for e in r['errors'] if e['kind']=='import']
classes=[e['header'].split('(',1)[1][:-1]for e in r['errors']if e['kind']=='setup_class']
import_actual=sum(sum(n.startswith(m+'.')for n in all_ids)for m in imports)
class_actual=sum(sum(n.startswith(c+'.')for n in all_ids)for c in classes)
expected=r['initial_tests']-len(imports)+import_actual+class_actual
repeat_ids=set(r['rerun_test_ids'])
newly_available_ids={n for n in all_ids if any(n.startswith(m+'.')for m in imports)
                                         or any(n.startswith(c+'.')for c in classes)}
real_initial_errors=[e for e in r['errors']if e['kind']=='test']
initial_run_passed=r['initial_tests']-len(imports)-len(real_initial_errors)
rerun_already_passed=len(repeat_ids-newly_available_ids)-len(real_initial_errors)
initial_log_end=(HERE/'full_regression.log').stat().st_mtime
source_mtime=(FAST/'tests/test_deferred_forest.py').stat().st_mtime
inventory=dict(inventory_only=True,tests_run_by_this_script=0,total_real_tests=len(all_ids),
 unique_test_ids=len(set(all_ids)),loader_errors=loader.errors,
 import_placeholder_tests=len(imports),actual_tests_in_import_failed_modules=import_actual,
 newly_available_setup_class_tests=class_actual,
 expected_total_from_initial=expected,expected_matches_inventory=expected==len(all_ids),
 initial_real_tests_passed=initial_run_passed,
 affected_module_real_tests=len(repeat_ids),affected_module_previously_passed_tests=rerun_already_passed,
 recovered_new_or_previously_errored_tests=len(repeat_ids)-rerun_already_passed,
 aggregate_distinct_passed=initial_run_passed+len(repeat_ids)-rerun_already_passed,
 deferred_forest_tests=[n for n in all_ids if n.startswith('test_deferred_forest.')],
 fifth_test='test_deferred_forest.DeferredForestTests.test_two_vertex_closed_walk_strict_example',
 fifth_test_source_modified_utc=datetime.fromtimestamp(source_mtime,timezone.utc).isoformat(),
 inferred_initial_test_run_start_utc=datetime.fromtimestamp(initial_log_end-372.442,timezone.utc).isoformat(),
 fifth_source_precedes_inferred_test_run_start_seconds=initial_log_end-372.442-source_mtime)
assert not loader.errors
assert inventory['aggregate_distinct_passed']==len(all_ids)
assert expected==len(all_ids)
assert r['cli_recovery']['successful']
r['final_inventory']=inventory
r['recovery_complete']=True
r['all_original_error_events_resolved']=True
path.write_text(json.dumps(r,indent=2)+'\n')
(HERE/'recovered_test_inventory.json').write_text(json.dumps(dict(summary=inventory,test_ids=all_ids),indent=2)+'\n')
print(json.dumps(inventory,indent=2))
