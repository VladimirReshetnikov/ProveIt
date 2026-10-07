#!/usr/bin/env python3
"""Exercise explicit verification guards by deliberate corruption in normal and -O runs.

Every tested failure must have its intended marker, nonzero exit status, and no
new success artifact. Additional input-file corruption tests exercise the strict
loader. This harness does not claim to enumerate every possible malformed input.
"""
import argparse
import ast
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parent.parent
CODE = ROOT/'code'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=ROOT/'build'/'guard_failure_checks.json')
args = parser.parse_args()
for source in sorted(CODE.glob('*.py')):
    if any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(source.read_text()))):
        raise RuntimeError(f'Optimization-sensitive assertion in {source.name}')
audits = ('hub_bound','rotation','double_hub','first_edge','partition_cut',
          'stored_small_rows','stored_completeness','stored_row_sum','ratio_decrease')
diagnostics = ('boundary_identities','one_defect_identity','python_root_row',
               'reference_total','union_integrality','union_range')
results = []


def fail_run(command,check,optimized,artifact):
    result = subprocess.run(command,text=True,capture_output=True,check=False)
    marker = f'CHECK_FAILED[{check}]'
    if result.returncode == 0 or marker not in result.stderr or artifact.exists():
        raise RuntimeError({'guard':check,'optimized':optimized,'returncode':result.returncode,
                            'expected_marker':marker,'success_artifact_exists':artifact.exists(),
                            'stderr':result.stderr})
    results.append({'guard':check,'optimized':optimized,'nonzero_exit':True,
                    'intended_failure_marker':True,'new_success_artifact_written':False})


with tempfile.TemporaryDirectory(prefix='report212-guards-') as temp:
    temporary = Path(temp)
    for optimized in (False,True):
        python = [sys.executable]+(['-O'] if optimized else [])
        for script,categories in (('independent_audit_checks.py',audits),('diagnostics.py',diagnostics)):
            for check in categories:
                output = temporary/f'{check}-{optimized}.json'
                command = python+[str(CODE/script),'--inject-failure',check,'--output',str(output)]
                fail_run(command,check,optimized,output)
        # Actual TSV mutation, rather than patching a verifier's return value.
        for case,check in (('format','data_format'),('negative','data_nonnegative'),
                           ('duplicate_root','data_duplicate'),('duplicate_moment','data_duplicate'),
                           ('missing','stored_completeness')):
            folder = temporary/f'{case}-{optimized}'
            shutil.copytree(ROOT/'data'/'fixture32',folder)
            roots = folder/('moments_exact.tsv' if case == 'duplicate_moment' else 'root_counts_exact.tsv')
            lines = roots.read_text().splitlines()
            if check == 'data_format':
                lines[0] = 'wrong\theader'
            elif check == 'data_nonnegative':
                lines[1] = '1\t1\t-1'
            elif check == 'data_duplicate':
                lines.append(lines[-1])
            else:
                lines.pop()
            roots.write_text('\n'.join(lines)+'\n')
            output = temporary/f'{case}-input-{optimized}.json'
            command = python+[str(CODE/'diagnostics.py'),'--data-dir',str(folder),'--output',str(output)]
            fail_run(command,check,optimized,output)
        # The selected small table can be reproduced using only the fixture.
        table = temporary/f'table-{optimized}'
        command = python+[str(CODE/'make_tables.py'),'--data-dir',str(ROOT/'data'/'fixture32'),
                          '--expected-max','32','--ks','16,32','--output-dir',str(table)]
        subprocess.run(command,check=True,capture_output=True,text=True)
        output_dir = temporary/f'corrupt-table-{optimized}'
        command = command[:-2]+['--output-dir',str(output_dir),'--compare',str(table/'table_values.json'),
                               '--inject-failure','table_comparison']
        fail_run(command,'table_comparison',optimized,output_dir/'table_values.json')
        duplicate = temporary/f'duplicate-json-{optimized}.json'
        original = (table/'table_values.json').read_text()
        duplicate.write_text('{"schema":"deliberate duplicate",'+original[1:])
        duplicate_output = temporary/f'duplicate-json-output-{optimized}'
        command = python+[str(CODE/'make_tables.py'),'--data-dir',str(ROOT/'data'/'fixture32'),
                          '--expected-max','32','--ks','16,32','--output-dir',str(duplicate_output),
                          '--compare',str(duplicate)]
        fail_run(command,'json_duplicate',optimized,duplicate_output/'table_values.json')
report = {'all_checks_passed':True,'assertion_ast_scan_passed':True,
          'failure_tests_passed':len(results),
          'method':'Named mathematical-value corruption, malformed TSVs, and exact table mismatch; require nonzero exit, intended marker, and no new success artifact.',
          'scope':'All nine enumerative audit categories, six diagnostics categories, five loader-corruption cases, exact table comparison, and duplicate JSON keys, each under normal Python and -O.',
          'tests':results}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'all_checks_passed':True,'failure_tests_passed':len(results)},indent=2))
