#!/usr/bin/env python3
"""One-command fixture replay or fresh C++/GMP regeneration, with scoped metadata."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
sys.dont_write_bytecode = True
from common import read_json_unique
ROOT = Path(__file__).resolve().parent.parent
CODE = ROOT/'code'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('mode', choices=('quick','regenerate'))
parser.add_argument('--max-k',type=int,choices=(256,512),default=256,
                    help='Fresh generation range; ignored in quick mode.')
parser.add_argument('--work-dir',type=Path,default=None,
                    help='New output directory; default build/quick-replay or build/regenerationN.')
args = parser.parse_args()
default_name = 'quick-replay' if args.mode == 'quick' else f'regeneration{args.max_k}'
work = (args.work_dir if args.work_dir is not None else ROOT/'build'/default_name).resolve()
if work == ROOT or work in ROOT.parents or (ROOT in work.parents and work != ROOT/'build' and ROOT/'build' not in work.parents):
    raise RuntimeError('CHECK_FAILED[work_directory_scope]: choose a fresh directory outside source inputs or under build/')
if work.exists():
    raise RuntimeError('CHECK_FAILED[work_directory_new]: output directory must not already exist')
work.mkdir(parents=True,exist_ok=False)
start = time.monotonic()
commands = []


def run(command,log,cwd=None):
    commands.append([str(x).replace(str(work), '{WORK}').replace(str(ROOT), '{ROOT}') for x in command])
    with (work/log).open('w') as stream:
        subprocess.run([str(x) for x in command],cwd=cwd,stdout=stream,stderr=subprocess.STDOUT,check=True)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


if args.mode == 'regenerate':
    n = args.max_k
    data = work/f'regenerated{n}'
    data.mkdir(parents=True,exist_ok=True)
    compiler = os.environ.get('CXX','g++')
    run([compiler,'--version'],'compiler_version.log')
    run([compiler,'-O3','-std=c++17',CODE/'moments.cpp','-lgmpxx','-lgmp','-o',work/'moments'],
        'compile.log')
    for optimized in (False,True):
        suffix = '_optimized' if optimized else ''
        run([sys.executable]+(['-O'] if optimized else [])+[CODE/'verify_cli_guards.py',
             '--binary',work/'moments','--output',work/f'cli_guard_checks{suffix}.json'],
            f'cli_guard_checks{suffix}.log')
    if (work/'cli_guard_checks.json').read_bytes() != (work/'cli_guard_checks_optimized.json').read_bytes():
        raise RuntimeError('CHECK_FAILED[optimized_output_equality]: CLI guards')
    run([work/'moments',str(n)],'generation.log',cwd=data)
    kind = 'fresh-generation'
else:
    n = 32
    data = ROOT/'data'/'fixture32'
    kind = 'fixture'
for script,label in (('independent_audit_checks.py','audit'),('diagnostics.py','diagnostics')):
    for optimized in (False,True):
        suffix = '_optimized' if optimized else ''
        command = [sys.executable]+(['-O'] if optimized else [])+[CODE/script,'--data-dir',data,
                   '--expected-max',str(n),'--data-kind',kind,'--output',work/f'{label}{suffix}.json']
        run(command,f'{label}{suffix}.log')
    if (work/f'{label}.json').read_bytes() != (work/f'{label}_optimized.json').read_bytes():
        raise RuntimeError(f'CHECK_FAILED[optimized_output_equality]: {label}')
for optimized in (False,True):
    suffix = '_optimized' if optimized else ''
    command = [sys.executable]+(['-O'] if optimized else [])+[CODE/'verify_guard_failures.py',
               '--output',work/f'guard_failure_checks{suffix}.json']
    run(command,f'guard_failure_checks{suffix}.log')
if (work/'guard_failure_checks.json').read_bytes() != (work/'guard_failure_checks_optimized.json').read_bytes():
    raise RuntimeError('CHECK_FAILED[optimized_output_equality]: corruption harness')
if args.mode == 'regenerate':
    for optimized in (False,True):
        suffix = '_optimized' if optimized else ''
        run([sys.executable]+(['-O'] if optimized else [])+[CODE/'make_tables.py',
             '--data-dir',data,'--expected-max',str(n),'--compare',ROOT/'tables'/'table_values.json',
             '--output-dir',work/f'tables{suffix}'],f'table_comparison{suffix}.log')
    # Check the full modest fixture prefix independently of decimal table values.
    for filename in ('moments_exact.tsv','root_counts_exact.tsv'):
        generated = (data/filename).read_text().splitlines()
        prefix = '\n'.join([generated[0]]+[line for line in generated[1:]
                             if int(line.split('\t')[0]) <= 32])+'\n'
        if prefix != (ROOT/'data'/'fixture32'/filename).read_text():
            raise RuntimeError(f'CHECK_FAILED[fixture_prefix]: {filename}')
    reference = read_json_unique(ROOT/'data'/'generation256_reference.json')
    for filename in ('moments_exact.tsv','root_counts_exact.tsv'):
        generated = (data/filename).read_text().splitlines()
        prefix = '\n'.join([generated[0]]+[line for line in generated[1:]
                             if int(line.split('\t')[0]) <= 256])+'\n'
        if hashlib.sha256(prefix.encode()).hexdigest() != reference[filename]:
            raise RuntimeError(f'CHECK_FAILED[full256_prefix_digest]: {filename}')
    if n == 512:
        run([sys.executable,CODE/'make_tables.py','--data-dir',data,'--expected-max','512',
             '--ks','16,32,64,128,256,512','--output-dir',work/'tables512'],'table512.log')
manifest = {
    'all_checks_passed':True,'mode':args.mode,
    'scope':{'direct_walk_enumeration_max_k':8,'independent_python_recurrence_max_k':16,
             'cpp_fresh_generation_max_k':n if args.mode == 'regenerate' else None,
             'input_consistency_max_k':n,'public_table_exact_regeneration_checked':args.mode == 'regenerate',
             'complete256_prefix_digests_checked':args.mode == 'regenerate',
             'higher_rows_are_not_independently_regenerated_by_a_second_algorithm':True},
    'normal_and_optimized_positive_outputs_identical':True,
    'deliberate_corruption_cases_per_harness_run':44,
    'cli_failure_cases_per_regeneration_run':15 if args.mode == 'regenerate' else None,
    'python_version':sys.version.split()[0],
    'cpp_source_sha256':sha(CODE/'moments.cpp'),
    'input_sha256':{name:sha(data/name) for name in ('moments_exact.tsv','root_counts_exact.tsv')},
    'table_reference_sha256':sha(ROOT/'tables'/'table_values.json'),
    'commands':commands,'elapsed_seconds':round(time.monotonic()-start,3)}
(work/'replay_metadata.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({key:manifest[key] for key in ('all_checks_passed','mode','scope','elapsed_seconds')},indent=2))
