#!/usr/bin/env python3
"""Exact and independent correctness checks for fast_cauchy.py."""
import importlib.util
import json
import random
import sys
from pathlib import Path
from fast_cauchy import FastCauchy, reconstruct


def need(ok, message):
    if not ok:
        raise AssertionError(message)


def load_historical(path):
    spec = importlib.util.spec_from_file_location('historical_joint_cauchy', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run(historical_path=None):
    stats = dict(modular_parameter_cases=0, modular_feature_entries=0,
                 reconstruction_checks=0, historical_cases=0,
                 historical_feature_entries=0, stress_cases=0)
    for a in range(1, 6):
        for i in range(a):
            for t in sorted(set([-3*(1<<i), -(1<<i), 1<<i, 3*(1<<i)])):
                if not -(1<<a) <= t < (1<<a):
                    continue
                for zeta in [(0,0), (1,0), (0,1), (1,1), (2,0), (3,-1)]:
                    for precision in (1, 3, 8, 31):
                        kernel = FastCauchy(a,i,t,precision,zeta)
                        fast = kernel.feature_tables()
                        naive = kernel.naive_feature_tables()
                        need(fast.target == naive.target, 'target != direct product')
                        need(fast.source == naive.source, 'source != direct product')
                        need(fast.stats['unit_inversions'] == 1, 'not one inversion')
                        need(fast.stats['recurrence_transitions'] == kernel.N*(kernel.N-1), 'transition count')
                        need(naive.stats['direct_product_steps'] == (kernel.N**3-kernel.N)//3, 'product count')
                        for j in range(kernel.N):
                            for k in range(kernel.N):
                                need(reconstruct(fast,kernel.ring,j,k) == kernel.direct_entry(j,k), 'matrix identity failed')
                                stats['reconstruction_checks'] += 1
                        stats['modular_parameter_cases'] += 1
                        stats['modular_feature_entries'] += 2*kernel.N**2
    # A zero residue must retain a unit internally; valuations are 0,1,0.
    kernel = FastCauchy(3,0,1,1,(1,0))
    values, residues = [], []
    v,u = kernel._start(2,1)
    for b in range(3):
        values.append(v); residues.append(kernel.ring.scale(u,v))
        if b < 2:
            v,u = kernel._next(b,2,1,v,u)
    need(values == [0,1,0], 'regression valuation sequence')
    need(residues[1] == (0,0) and residues[2] != (0,0), 'recovery after zero')
    stats['transient_zero_regression'] = {'valuations': values, 'residues': residues}
    # Larger dimensions, high valuations of zeta, negative and large lifts.
    rng = random.Random(20261026)
    for a in (6,7,8):
        for i in sorted(set([0, a//2, a-1])):
            for precision in (2,17,64,129):
                zeta = (rng.randrange(-10000,10000)*(1<<9), rng.randrange(-10000,10000)*(1<<9))
                kernel = FastCauchy(a,i,1<<i,precision,zeta)
                tables = kernel.feature_tables()
                for _ in range(48):
                    j,k = rng.randrange(kernel.N),rng.randrange(kernel.N)
                    need(reconstruct(tables,kernel.ring,j,k) == kernel.direct_entry(j,k), 'stress identity')
                    stats['reconstruction_checks'] += 1
                stats['stress_cases'] += 1
    if historical_path:
        hist = load_historical(historical_path)
        for a in range(1,5):
            for i in range(a):
                for t in (-(1<<i),1<<i):
                    for zeta in ((0,0),(1,0),(0,1),(2,0),(3,-1)):
                        kernel = FastCauchy(a,i,t,37,zeta)
                        tables = kernel.feature_tables()
                        old = hist.JointCauchyKernel(a,i,t,hist.Quadratic(*zeta))
                        target,source = old.feature_tables()
                        old_target = [[hist.residue(x,37) for x in row] for row in target]
                        old_source = [[hist.residue(x,37) for x in row] for row in source]
                        need(tables.target == old_target, 'historical target mismatch')
                        need(tables.source == old_source, 'historical source mismatch')
                        stats['historical_cases'] += 1
                        stats['historical_feature_entries'] += 2*kernel.N**2
    stats['status'] = 'PASS'
    stats['scope'] = 'Finite exact local algebra checks; not a complete SAT solver or a formal proof.'
    return stats

if __name__ == '__main__':
    hist = sys.argv[1] if len(sys.argv)>1 else None
    print(json.dumps(run(hist), indent=2))
