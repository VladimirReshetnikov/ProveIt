#!/usr/bin/env python3
"""Paired local-feature benchmarks; no SAT runtime claim is made.

The exact reference is the archived joint_cauchy.py unchanged. The second
control is a strengthened adaptation of its independent rational recurrence
with the same safe cutoff. Each exact method's timed work includes reduction
to the finite-precision output required by the task. Every pair is checked
for exact output equality before its timing can be reported.
"""
import argparse
from fractions import Fraction
import gc
import hashlib
import json
from pathlib import Path
import platform
import statistics
import time

from modular_cauchy import ModularCauchy
from reference_joint_cauchy import JointCauchyKernel, Quadratic, residue
from reference_recurrence import feature_tables as recurrence_tables


def reduce_tables(tables, p, B):
    return tuple([[residue(x, p) for x in row] for row in table[:B]] for table in tables)


def run_case(a, i, p, zeta, repeats, original=True):
    t = 1 << i
    z = Fraction(zeta[0]) if zeta[1] == 0 else Quadratic(*zeta)
    B = ModularCauchy(a, i, t, zeta, p).B
    methods = {}
    if original:
        methods['archived_full_exact'] = lambda: reduce_tables(JointCauchyKernel(a, i, t, z).feature_tables(), p, B)
    methods['exact_recurrence_same_cutoff'] = lambda: reduce_tables(recurrence_tables(JointCauchyKernel(a, i, t, z), p), p, B)
    methods['modular_cached_separate_inverses'] = lambda: ModularCauchy(a, i, t, zeta, p, False).feature_tables()
    methods['modular_cached_batch_inverse'] = lambda: ModularCauchy(a, i, t, zeta, p, True).feature_tables()
    checksums = {}
    reference = None
    # One complete warmup per method, with output comparison outside timing.
    for name, method in methods.items():
        result = method()
        if reference is None:
            reference = result
        if result != reference:
            raise ArithmeticError(f'{name}: output does not match')
        checksums[name] = hashlib.sha256(repr(result).encode()).hexdigest()
    measurements = {name:[] for name in methods}
    cpu_measurements = {name:[] for name in methods}
    # Interleave methods in alternating order to reduce drift bias.
    for repetition in range(repeats):
        ordered = list(methods.items())
        if repetition % 2:
            ordered.reverse()
        for name, method in ordered:
            gc.collect()
            cpu_start = time.process_time_ns()
            start = time.perf_counter_ns()
            result = method()
            elapsed = (time.perf_counter_ns()-start)/1e9
            cpu_elapsed = (time.process_time_ns()-cpu_start)/1e9
            if result != reference:
                raise ArithmeticError(f'{name}: timed output changed')
            measurements[name].append(elapsed)
            cpu_measurements[name].append(cpu_elapsed)
    medians = {name:statistics.median(samples) for name, samples in measurements.items()}
    fast = medians['modular_cached_batch_inverse']
    op_kernel = ModularCauchy(a, i, t, zeta, p)
    op_kernel.feature_tables()
    return {'a':a, 'i':i, 'N':1 << (a-1), 'p':p, 'zeta':list(zeta), 'B':B,
            'median_seconds':medians, 'samples_seconds':measurements,
            'median_cpu_seconds':{name:statistics.median(samples) for name,samples in cpu_measurements.items()},
            'samples_cpu_seconds':cpu_measurements,
            'speedup_vs_batch':{name:elapsed/fast for name, elapsed in medians.items()},
            'digest':checksums['modular_cached_batch_inverse'],
            'all_outputs_equal':len(set(checksums.values())) == 1,
            'modular_ring_multiplications':op_kernel.ring.multiplies,
            'modular_ring_inversions':op_kernel.ring.inversions,
            'prefactor_scalar_inversions':op_kernel.scalar_inversions,
            'total_modular_inversions':op_kernel.ring.inversions+op_kernel.scalar_inversions,
            'distinct_cached_denominators':len(op_kernel._den),
            'output_pair_entries':2*op_kernel.N*B}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('benchmark.json'))
    args = parser.parse_args()
    if args.repeats < 1:
        raise ValueError('repeats must be positive')
    cases = [(5,0,32,(1,0)), (5,0,32,(0,1)),
             (6,0,64,(1,0)), (6,0,64,(0,1)),
             (7,1,64,(1,0)), (7,1,64,(0,1))]
    if args.quick:
        cases = cases[:2]
    result = {'python':platform.python_version(), 'platform':platform.platform(),
              'repeats':args.repeats, 'warmups':1,
              'timing_clock':'perf_counter_ns',
              'scope':'Local Cauchy feature tables modulo 2^p; neither SAT runtime nor complete contraction runtime.',
              'controls':'Original full exact routine plus an O(N*B) exact recurrence adapted from the existing independent verifier with the same cutoff.',
              'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in Path(__file__).parent.glob('*.py')},
              'cases':[]}
    cpuinfo = Path('/proc/cpuinfo')
    if cpuinfo.exists():
        result['cpu_model'] = next((line.split(':',1)[1].strip()
                                    for line in cpuinfo.read_text().splitlines()
                                    if line.startswith('model name')), 'unknown')
    for a,i,p,zeta in cases:
        case=run_case(a,i,p,zeta,args.repeats)
        result['cases'].append(case)
        print(json.dumps({'N':case['N'],'zeta':zeta,'B':case['B'],
                          'median_seconds':case['median_seconds'],
                          'speedup_vs_batch':case['speedup_vs_batch']}),flush=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__ == '__main__':
    main()
