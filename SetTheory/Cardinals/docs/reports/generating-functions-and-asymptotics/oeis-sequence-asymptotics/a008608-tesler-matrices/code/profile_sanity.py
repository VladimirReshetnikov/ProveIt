#!/usr/bin/env python3
"""Floating-point sanity only; no directed rounding or asymptotic certification.

Recomputes the genuine M=1024 entropy profile and simultaneous triangles.
Requires NumPy. Output is deterministic in the recorded environment, though
last-bit differences across BLAS/NumPy/platform versions are possible.
"""
import argparse
import json
import math
from pathlib import Path
import numpy as np

M = 1024
c = math.pi / math.sqrt(6)

def require(condition, message):
    if not condition:
        raise ValueError(message)

def h(values):
    v = np.asarray(values, dtype=float)
    require(bool(np.all(np.isfinite(v))), 'Nonfinite entropy input')
    require(bool(np.all(v >= 0)), 'Negative entropy input')
    out = np.log1p(v)
    positive = v > 0
    out[positive] += v[positive] * np.log1p(1 / v[positive])
    return out

def run(n):
    require(n >= M + 1, 'n must exceed the fixed cutoff')
    # F[a-1,b-1] is interval [a,b], equivalently edge (a-1,b).
    F = np.zeros((n,n))
    diff = np.zeros(n+1)
    for a in range(M,n+1):
        t = np.arange(1,n-a+2) * c / math.sqrt(a)
        q = np.exp(-t) / (-np.expm1(-t))
        F[a-1,a-1:] = q
        diff[a-1] += q.sum()
        diff[a:] -= q
    loads = np.cumsum(diff)[:n]
    gaps = np.arange(1,n+1) - loads
    require(float(np.min(gaps)) >= -1e-8, 'Negative completion gap')
    F[np.diag_indices(n)] += gaps
    rows = F.sum(axis=1)
    columns = F.sum(axis=0)
    require(bool(np.allclose(rows[1:]-columns[:-1],1,rtol=0,atol=1e-8)), 'Base netflow mismatch')
    require(bool(np.allclose(rows[:M],np.arange(1,M+1),rtol=0,atol=1e-8)), 'Initial margin mismatch')
    initial_entropy = float(h(F).sum())
    chosen = rows.copy()
    logchoices = 0.0
    for j in range(M,n):
        w = F[j-1,j]
        lo, hi = math.ceil(rows[j]), math.floor(rows[j]+w/2)
        require(hi >= lo, 'Empty integer choice set')
        logchoices += math.log(hi-lo+1)
        newrho = (lo+hi)//2
        t = newrho-rows[j]
        require(0 <= t <= w/2+1e-10, 'Triangle parameter out of range')
        chosen[j] = newrho
        F[j-1,j] -= t
        F[j-1,j-1] += t
        F[j,j] += t
    newrows = F.sum(axis=1)
    newcolumns = F.sum(axis=0)
    final_entropy = float(h(F).sum())
    require(bool(np.allclose(newrows,chosen,rtol=0,atol=1e-8)), 'Outgoing margin cross-coupling')
    require(bool(np.allclose(newrows[1:]-newcolumns[:-1],1,rtol=0,atol=1e-8)), 'Final netflow mismatch')
    require(bool(np.allclose(newrows,np.round(newrows),rtol=0,atol=1e-8)), 'Noninteger outgoing margins')
    require(bool(np.allclose(newcolumns,np.round(newcolumns),rtol=0,atol=1e-8)), 'Noninteger incoming margins')
    require(final_entropy >= initial_entropy-(n-M)*math.log(2)-1e-8, 'Entropy-loss inequality mismatch')
    return {'n': n, 'fixed_cutoff': M, 'base_entropy': initial_entropy,
            'final_entropy': final_entropy, 'entropy_loss': initial_entropy-final_entropy,
            'entropy_loss_bound': (n-M)*math.log(2),
            'log_integer_margin_choices': logchoices,
            'maximum_netflow_residual': float(np.max(abs(newrows[1:]-newcolumns[:-1]-1))),
            'maximum_outgoing_integer_residual': float(np.max(abs(newrows-np.round(newrows)))),
            'minimum_final_entry': float(F.min())}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    result = {'status': 'sanity_pass', 'evidence_kind': 'floating_point_only',
              'numpy_version': np.__version__, 'results': [run(2048), run(4096)]}
    data = json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(data)
    else:
        print(data,end='')
if __name__ == '__main__':
    main()
