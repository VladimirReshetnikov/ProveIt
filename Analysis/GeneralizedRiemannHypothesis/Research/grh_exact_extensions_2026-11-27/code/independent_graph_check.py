"""Independent numerical diagnostics; they do not replace the proof."""
import json
from pathlib import Path
import numpy as np

rng = np.random.default_rng(27112026)

def covariance(d):
    return np.diag(d) - np.outer(d, d) / sum(d)

def positive_power(C, exponent):
    s, U = np.linalg.eigh(C)
    s = np.where(s > 1e-10, np.maximum(s, 0) ** exponent, 0)
    return (U * s) @ U.T

def pinv(L):
    s, U = np.linalg.eigh(L)
    si = np.divide(1, s, where=s > 1e-10, out=np.zeros_like(s))
    return (U * si) @ U.T

def eigen_nonnegative(B):
    s = np.linalg.eigvalsh(B)
    assert min(s) > -1e-8
    return np.maximum(s, 0)

def normp(s, p):
    return max(s) if p == float('inf') else sum(s ** p) ** (1/p)

records = []
checks = 0
max_relative_optimum_error = 0.
for n in range(2, 7):
    for repetition in range(10):
        d = rng.integers(1, 5, size=n)
        N = sum(d)
        W = float(rng.uniform(.3, 5.))
        C = covariance(d)
        R = positive_power(C, .5)
        V = np.zeros((N, n))
        labels = np.repeat(np.arange(n), d)
        V[np.arange(N), labels] = 1
        # QR with first vector constant gives a basis of its perpendicular space.
        Z, _ = np.linalg.qr(np.column_stack([np.ones(N), np.eye(N)[:, :-1]]))
        U = Z[:, 1:]
        roots = np.sort(rng.normal(size=N))
        A = U.T @ np.diag(roots) @ U
        beta = np.linalg.eigvalsh(A)
        for p in [1., 1.5, 2., 3., float('inf')]:
            r = 1. if p == float('inf') else p/(p+1)
            Cr = positive_power(C, r)
            Lopt = 2 * W * Cr / np.trace(Cr)
            assert np.max(Lopt - np.diag(np.diag(Lopt))) < 1e-9
            bopt = eigen_nonnegative(R @ pinv(Lopt) @ R)
            theory = np.trace(Cr)/(2*W) if p == float('inf') else np.trace(Cr)**(1+1/p)/(2*W)
            actual = normp(bopt, p)
            max_relative_optimum_error = max(max_relative_optimum_error, abs(actual/theory - 1))
            assert abs(actual/theory - 1) < 1e-8
            # Arbitrary connected complete competitors; sparse graphs also included.
            for competitor in range(8):
                edges = rng.uniform(.01, 1., size=(n, n))
                edges = np.triu(edges, 1)
                if competitor == 0:
                    edges = np.diag(rng.uniform(.1, 1., size=n-1), 1)
                edges *= W / edges.sum()
                edges += edges.T
                L = np.diag(edges.sum(axis=1)) - edges
                M = U.T @ V @ pinv(L) @ V.T @ U
                bm = eigen_nonnegative(M)
                assert normp(bm, p) >= theory * (1 - 1e-8)
                lam = np.linalg.eigvalsh(A-M)
                shifts = beta-lam
                assert min(shifts) > -1e-8
                shifts = np.maximum(shifts, 0)
                assert normp(shifts, p) <= normp(bm, p) * (1+1e-8)
                # Zero configuration gives exact worst-case transport.
                assert abs(normp(np.maximum(-np.linalg.eigvalsh(-M), 0), p)-normp(bm,p)) < 1e-7
                checks += 1
        records.append({'vertices': n, 'degrees': d.tolist(), 'budget': W})

out = {'seed': 27112026, 'random_degree_profiles': len(records),
       'graph_objective_checks': checks,
       'max_relative_optimum_error': max_relative_optimum_error,
       'status': 'pass',
       'note': 'Numerical diagnostics only. All root multiplicities are retained; empirical W_p is obtained by dividing the p norm by (N-1)^(1/p).'}
path = Path(__file__).resolve().parents[1]/'results'/'independent_graph_check.json'
path.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2))
