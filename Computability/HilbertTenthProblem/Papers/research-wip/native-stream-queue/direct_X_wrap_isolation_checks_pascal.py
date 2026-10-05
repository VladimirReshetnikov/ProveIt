#!/usr/bin/env python3
"""Fresh scalar formulas only; no source/helper/array loading or evaluation."""
import json
import hashlib
from functools import lru_cache
from pathlib import Path

SCALE = 10**60
TERMS = 70

def ceildiv(a, b):
    return -(-a // b)

def atanh_twice_bounds(a, b):
    # 0 <= a/b <= 1/3. All returned endpoints are integer / SCALE.
    if not (0 <= 3*a <= b):
        raise ValueError("range")
    lo, hi = a*SCALE//b, ceildiv(a*SCALE, b)
    lo2, hi2 = lo*lo//SCALE, ceildiv(hi*hi, SCALE)
    tlo, thi = lo, hi
    total_lo = total_hi = 0
    for j in range(TERMS):
        total_lo += tlo//(2*j+1)
        total_hi += ceildiv(thi, 2*j+1)
        tlo = tlo*lo2//SCALE
        thi = ceildiv(thi*hi2, SCALE)
    # The omitted 2*sum r^(2j+1)/(2j+1) is < 3^(-2*TERMS).
    tail = ceildiv(SCALE, 3**(2*TERMS))
    return 2*total_lo, 2*total_hi+tail

LOG2 = atanh_twice_bounds(1, 3)

@lru_cache(None)
def log_bounds(n):
    if n < 1:
        raise ValueError("log domain")
    e = n.bit_length()-1
    b = 1 << e
    lo, hi = atanh_twice_bounds(n-b, n+b)
    return e*LOG2[0]+lo, e*LOG2[1]+hi

def integer_interval(q, X, s, v, epsilon):
    Y = s*q**3
    E = X*Y
    A, P = Y*(X+1)+2, 2*X*Y*Y+1
    al, au = log_bounds(2*A)
    pl, pu = log_bounds(2*P)
    ll, lu = 2*al-pu, 2*au-pl
    if ll <= 0:
        raise ValueError("nonpositive slope")
    err = ceildiv(SCALE*q**4, A*A)+ceildiv(SCALE*q**4, P*P)
    d = epsilon+v*E-2
    if d <= 0:
        raise ValueError("wrapped coefficient")
    nl = 2*log_bounds(4*A*Y)[0]+d*pl-2*err
    nu = 2*log_bounds(4*A*(Y+1))[1]+d*pu+2*err
    low, high = nl//lu+1, ceildiv(nu, ll)-1
    return low, high

def main():
    dependencies = [
        Path('/tmp/complete83_direct_X_boundary_pascal.md'),
        Path('/tmp/complete83_direct_X_boundary_pascal.json'),
        Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json'),
    ]
    pins = [dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
            for p in dependencies]
    pell_controls = 0
    for A in range(2, 18):
        previous, current = 0, 1
        al, au = log_bounds(2*A)
        for j in range(1, 33):
            pl, pu = log_bounds(current)
            if not ((pl-(j-1)*au)*A*A > -j*SCALE and
                    (pu-(j-1)*al)*A*A < j*SCALE):
                raise RuntimeError('Pell logarithm control')
            pell_controls += 1
            previous, current = current, 2*A*current-previous
    total = parity_pruned = singleton = outside_outer = projection_pass = 0
    candidates = []
    singleton_records = []
    per_q = []
    for q in range(16, 65, 2):
        q_total = q_single = q_project = 0
        for X in range(1, q):
            for s in range(1, (q-1)//X+1):
                Y, E = s*q**3, X*s*q**3
                # vE<R<q^4 gives this exact finite upper bound.
                for v in range(1, (q-1)//(X*s)+1):
                    for epsilon in (-1, 1):
                        total += 1
                        q_total += 1
                        lo, hi = integer_interval(q, X, s, v, epsilon)
                        if hi-lo >= 1:
                            raise RuntimeError("more than one integer")
                        if lo > hi:
                            continue
                        singleton += 1
                        q_single += 1
                        R = lo
                        singleton_records.append(dict(q=q, X=X, s=s, v=v,
                            epsilon=epsilon, R=R,
                            outer_lower=(2*q-1)*(q*q-1),
                            outer_upper=q**4-q**3))
                        if not ((2*q-1)*(q*q-1) < R < q**4-q**3):
                            outside_outer += 1
                            continue
                        if R % 2 == 0 or (R+epsilon+v*E) % 2:
                            parity_pruned += 1
                            continue
                        H = 4*Y*(X+1)+3
                        passed = pow(2, R, H) == X
                        projection_pass += int(passed)
                        q_project += int(passed)
                        candidates.append(dict(q=q, X=X, s=s, v=v,
                                               epsilon=epsilon, R=R,
                                               main_projection=passed))
        per_q.append(dict(q=q, tuples=q_total,
                          singleton_intervals=q_single,
                          projection_passes=q_project))
    return dict(scope="Necessary-condition superset only; no source arrays or full zeros evaluated",
                author_helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                dependencies=pins,
                q_range="even integers 16 through 64 inclusive",
                exact_log_method="integer outward-rounded atanh series, 70 terms, scale 10^60",
                tuples=total, singleton_intervals=singleton,
                outside_outer=outside_outer, parity_rejections=parity_pruned,
                main_projection_passes=projection_pass,
                exact_pell_log_controls=pell_controls,
                singleton_records=singleton_records,
                candidates=candidates, per_q=per_q,
                source_arrays_executed=False, predecessor_helpers_executed=False)

if __name__ == "__main__":
    print(json.dumps(main(), indent=2, sort_keys=True))
