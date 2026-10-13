"""Repeat exactly the three subprocess checks whose initial harness cwd was wrong."""
from pathlib import Path
import contextlib
import json
import os
import sys
import time
import unittest
HERE=Path(__file__).resolve().parent
FAST=HERE.parent/'ProveIt/Topology/UnknotRecognition/fast'
sys.path[:0]=[str(FAST/'tests'),str(FAST)]
os.chdir(FAST)
path=HERE/'failed_module_recovery.json'
r=json.loads(path.read_text())
names=[
 'test_closure_scan.ClosureTests.test_cli_dispatch_and_invalid_budget',
 'test_shadow_scan.ShadowTests.test_recognizer_and_cli_route_to_marked_backend',
 'test_source_handle_reduction.SourceHandleTests.test_cli_handle_stage_and_strict_option']
start=time.perf_counter()
with (HERE/'failed_cli_tests_rerun.log').open('w') as log:
 with contextlib.redirect_stdout(log),contextlib.redirect_stderr(log):
  result=unittest.TextTestRunner(stream=log,verbosity=2).run(
   unittest.defaultTestLoader.loadTestsFromNames(names))
r['cli_recovery']=dict(test_ids=names,command='python research_integration/rerun_cli_failures.py',
 cause='The first recovery harness modified only its own sys.path while running from scratch; three child Python CLI processes could not import fastunknot. Restored expected cwd=fast and repeated exactly these checks.',
 tests_run=result.testsRun,errors=len(result.errors),failures=len(result.failures),
 seconds=time.perf_counter()-start,successful=result.wasSuccessful())
path.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r['cli_recovery']))
sys.exit(0 if result.wasSuccessful() else 1)
