#!/usr/bin/env python3
"""Explicit finite checks: Python regeneration <=16; larger input consistency only."""
import argparse
import json
from pathlib import Path
from common import (bells, load_rows, python_recurrence, read_table, require,
                    threshold_s, union_counts)
ROOT = Path(__file__).resolve().parent.parent
CHECKS = ('boundary_identities','one_defect_identity','python_root_row',
          'reference_total','union_integrality','union_range')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data-dir', type=Path, default=ROOT/'data'/'fixture32')
parser.add_argument('--expected-max', type=int, default=32)
parser.add_argument('--data-kind', choices=('fixture','fresh-generation','stored'), default='fixture')
parser.add_argument('--output', type=Path, default=ROOT/'build'/'diagnostics.json')
parser.add_argument('--inject-failure', choices=CHECKS)
args = parser.parse_args()
M,F = load_rows(args.data_dir,args.expected_max)
B = bells(args.expected_max+1)
for k in range(1,args.expected_max+1):
    require(sum(F[k].values()) == M[k], 'stored_row_sum',k)
    star = F[k][k]+(args.inject_failure == 'boundary_identities')
    require(star == B[k] and F[k][1] == M[k-1], 'boundary_identities',k)
    if k >= 2:
        defect = F[k][k-1]+(args.inject_failure == 'one_defect_identity')
        require(defect == (k-1)*B[k-1], 'one_defect_identity',k)
P = python_recurrence(16)
for k in range(1,17):
    candidate = P[k][1:k+1]
    if args.inject_failure == 'python_root_row':
        candidate[0] += 1
    require(candidate == [F[k][m] for m in range(1,k+1)], 'python_root_row',k)
for k,value in read_table(ROOT/'data'/'reference_totals_k16.tsv',['k','M2k']):
    candidate = value+(args.inject_failure == 'reference_total')
    require(candidate == M[k], 'reference_total',k)
union_cases = 0
for k in (4,8,16,24,32,64,128,256,512):
    if k not in M:
        continue
    for family in ('quarter','log_squared'):
        if union_counts(k,k-threshold_s(k,family),F,M[k],args.inject_failure) is not None:
            union_cases += 1
result = {
    'all_checks_passed':True,
    'scope':{'input_kind':args.data_kind,
             'input_consistency_max_k':args.expected_max,
             'independent_python_recurrence_max_k':16,
             'reference_totals_max_k':16,
             'this_script_does_not_regenerate_cpp_rows':True},
    'checks':['complete index sets and no duplicate records','nonnegative integer entries',
              'all root row sums','one-excursion and star boundaries','one-defect identity',
              'all Python recurrence row entries through16','pinned reference totals through16',
              'finite union integrality and range'],
    'union_cases_passed':union_cases,
    'guard_mode':'Explicit runtime checks; no assert statements.'}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
