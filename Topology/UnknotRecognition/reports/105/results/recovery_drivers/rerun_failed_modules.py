"""Rerun only modules with errors in the initial sparse-checkout regression."""
from pathlib import Path
import contextlib
import json
import os
import sys
import time
import unittest

HERE = Path(__file__).resolve().parent
FAST = HERE.parent / 'ProveIt/Topology/UnknotRecognition/fast'
sys.path[:0] = [str(FAST / 'tests'), str(FAST)]
os.chdir(FAST)
REPORT = HERE / 'failed_module_recovery.json'
record = json.loads(REPORT.read_text())
loader = unittest.TestLoader()
suites = [(name, loader.loadTestsFromName(name)) for name in record['modules']]

def ids(suite):
    if isinstance(suite, unittest.TestSuite):
        return [name for child in suite for name in ids(child)]
    return [suite.id()]

record['rerun_module_test_counts'] = {name: suite.countTestCases() for name,suite in suites}
record['rerun_test_ids'] = [name for _,suite in suites for name in ids(suite)]
record['rerun_preparation_errors'] = loader.errors
record['rerun_command'] = 'python research_integration/rerun_failed_modules.py'
if loader.errors:
    REPORT.write_text(json.dumps(record,indent=2)+'\n')
    raise RuntimeError('Failed module still has an import error after baseline restoration')
print('Rerunning',len(suites),'affected modules with',len(record['rerun_test_ids']),'tests',flush=True)
start = time.perf_counter()
with (HERE/'failed_modules_rerun.log').open('w') as log:
    with contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
        result = unittest.TextTestRunner(stream=log,verbosity=2).run(
            unittest.TestSuite(suite for _,suite in suites))
record['rerun_result'] = dict(tests_run=result.testsRun,errors=len(result.errors),
    failures=len(result.failures),skipped=len(result.skipped),seconds=time.perf_counter()-start,
    successful=result.wasSuccessful(),
    error_details=[dict(test=str(t),traceback=tb)for t,tb in result.errors],
    failure_details=[dict(test=str(t),traceback=tb)for t,tb in result.failures])
REPORT.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record['rerun_result']),flush=True)
sys.exit(0 if result.wasSuccessful() else 1)
