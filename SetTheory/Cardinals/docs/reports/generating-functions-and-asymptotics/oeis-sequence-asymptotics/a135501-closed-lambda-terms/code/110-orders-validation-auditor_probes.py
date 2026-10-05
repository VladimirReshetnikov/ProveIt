#!/usr/bin/env python3
"""Independent exact finite probes and isolated fault injection for report110.
This is a finite validation aid, not an asymptotic proof or a tamper-proof verifier.
All probe mutations are confined to temporary copies; the checker and fixtures
are hashed before and after. Guards use explicit exceptions, including under -O.
"""
import ast
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def snapshot():
    paths = [ROOT / 'check.py'] + sorted((ROOT / 'data').iterdir())
    return {p.relative_to(ROOT).as_posix(): sha256(p.read_bytes()).hexdigest()
            for p in paths if p.is_file()}

# Scalar series use a separately coded reciprocal and log-derivative identity.
def multiply(a, b, d):
    c = [F(0)] * (d + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j <= d:
                c[i + j] += x * y
    return c

def reciprocal(a, d):
    require(a[0] != 0, 'scalar reciprocal domain')
    c = [1 / F(a[0])]
    for n in range(1, d + 1):
        c.append(-sum(a[k] * c[n-k] for k in range(1, min(n, len(a)-1) + 1)) / a[0])
    return c

def logarithm(a, d):
    require(a[0] == 1, 'scalar logarithm domain')
    derivative = [F(k) * a[k] for k in range(1, len(a))]
    quotient = multiply(derivative, reciprocal(a, d), d)
    return [F(0)] + [quotient[k-1] / k for k in range(1, d + 1)]

def exponential(a, d):
    require(a[0] == 0, 'scalar exponential domain')
    c = [F(1)] + [F(0)] * d
    power = c[:]
    fact = 1
    for k in range(1, d + 1):
        fact *= k
        power = multiply(power, a, d)
        c = [v + w / fact for v, w in zip(c, power)]
    return c

def evaluate(poly, z):
    return sum(F(c) * z**i for i, c in enumerate(poly))

def scalar_reversion(z, order, A=None):
    values = []
    for j in range(1, order + 1):
        U = [F(1), -z] + values + [F(0)] * order
        U = U[:j+1]
        if A is None:
            coefficient = logarithm(U, j)[j]
        else:
            # log(U^2 + A*x*U + x^2), without the checker's split logs.
            core = multiply(U, U, j)
            for k in range(1, j+1):
                core[k] += A * U[k-1]
            if j >= 2:
                core[2] += 1
            coefficient = logarithm(core, j)[j]
        values.append(-coefficient)
    return values

def algebra_probes():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('report110_checked_module', ROOT / 'check.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    source = (ROOT / 'check.py').read_text()
    tree = ast.parse(source)
    require(not any(isinstance(n, ast.Assert) for n in ast.walk(tree)), 'assert used as checker guard')
    require(not any(isinstance(n, ast.Constant) and isinstance(n.value, float) for n in ast.walk(tree)),
            'floating-point checker literal')
    p, P = module.forward(8, 'log')
    q_by_A = {A: module.inverse(6, A, 'log') for A in (F(-3,2), F(-1))}
    comparisons = 0
    for z in map(F, [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]):
        scalar_p = scalar_reversion(z, 8)
        require(scalar_p == [evaluate(poly, z) for poly in p], 'independent scalar forward reversion')
        U = [F(1), -z] + scalar_p
        R = reciprocal(U, 8)
        require([scalar_p[j-1] + R[j-1] for j in range(1, 9)] == [evaluate(poly, z) for poly in P],
                'independent scalar forward correction')
        product = multiply(U, exponential([F(0)] + scalar_p, 8), 8)
        require(product == [F(1)] + [F(0)] * 8, 'independent forward exponential residual')
        comparisons += 3
        for A, q in q_by_A.items():
            scalar_q = scalar_reversion(z, 6, A)
            require(scalar_q == [evaluate(poly, z) for poly in q], 'independent scalar inverse reversion')
            U = [F(1), -z] + scalar_q
            core = multiply(U, U, 6)
            for k in range(1, 7):
                core[k] += A * U[k-1]
            core[2] += 1
            product = multiply(core, exponential([F(0)] + scalar_q, 6), 6)
            require(product == [F(1)] + [F(0)] * 6, 'independent inverse exponential residual')
            comparisons += 2
    # PGF derivatives give each component's mean and second factorial moment.
    for u in range(1, 101):
        total_mean = F(0)
        total_var = F(0)
        for m in range(u):
            p0 = F(m, u)
            mean = p0 / (2 * (1-p0))
            factorial_second = 3 * p0*p0 / (4 * (1-p0)**2)
            variance = factorial_second + mean - mean*mean
            require(variance == F(m*u, 2*(u-m)**2), 'PGF component variance')
            total_mean += mean
            total_var += variance
        H1 = sum(F(1,k) for k in range(1,u+1))
        H2 = sum(F(1,k*k) for k in range(1,u+1))
        require(total_mean == F(u,2) * (H1-1), 'PGF summed mean')
        require(total_var == F(u*u,2)*H2 - F(u,2)*H1, 'PGF summed variance')
        require(total_var <= u*u, 'PGF variance bound')
    return comparisons

# Each source defect must fail at the named mathematical check, before fixtures.
MUTATIONS = [
    ('direct_unary_index', 'value+=direct(m+1,u-1,b)', 'value+=direct(m+2,u-1,b)', 'size recurrence or parity'),
    ('parity_selection', 'if (N-u)%r==0)', 'if True)', 'size recurrence or parity'),
    ('shape_binary_index', 'D[u][q1+q2+1,max(h1,h2)]+=v1*v2', 'D[u][q1+q2+2,max(h1,h2)]+=v1*v2', 'shape count'),
    ('tree_unary_depth', 'return [m]+intern,leaves,q', 'return [m+1]+intern,leaves,q', 'tree structure'),
    ('coarse_radical_factor', 'radical/=1-F(m,u)', 'radical*=F(2)/(1-F(m,u))', 'coarse radical bound'),
    ('height_radical_bound', 'bound=F(h**h,factorial(h))*delta**(-2*d)', 'bound=F(h**h,factorial(h))*delta**(-2*d)/2', 'height radical bound'),
    ('height_unary_index', 'reduced(m+1,u-1,h-1)', 'reduced(m+2,u-1,h-1)', 'direct and reduced recurrence'),
    ('spine_factor_index', 'Q=mul(Q,[comb(2*j,j)*m**j', 'Q=mul(Q,[comb(2*j,j)*(m+1)**j', 'spine subclass'),
    ('convolution_denominator', 'F(Q[j],(4*u)**j)', 'F(Q[j],(2*u)**j)', 'Catalan convolution'),
    ('moment_mean_factor', 'F(m,2*(u-m))', 'F(m,3*(u-m))', 'negative binomial mean'),
    ('moment_variance_factor', 'F(m*u,2*(u-m)**2)', 'F(m*u,(u-m)**2)', 'negative binomial variance'),
    ('forward_reversion_sign', 'p.append(ps(coefficient,-1))', 'p.append(ps(coefficient,1))', 'forward residual'),
    ('exponential_divisor', 'F(j,n)))', 'F(j,n+1)))', 'forward residual'),
    ('inverse_log_factor', 'ss(slog(U,d),2)', 'ss(slog(U,d),3)', 'inverse residual'),
    ('inverse_quadratic_sign', 'core[2]=pa(core[2],ONE)', 'core[2]=pa(core[2],ps(ONE,-1))', 'inverse residual'),
    ('printed_coefficient_sign', '(0,0,F(-1,2),F(1,3))', '(0,0,F(1,2),F(1,3))', 'printed forward coefficients'),
]

def execute(copy, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + ['check.py']
    return subprocess.run(command, cwd=copy, text=True, capture_output=True, timeout=40)

def expect_failure(copy, optimized, name, expected):
    completed = execute(copy, optimized)
    require(completed.returncode != 0, f'undetected fault: {name}')
    require(f'RuntimeError: {expected}' in completed.stderr, f'wrong failure for {name}: {completed.stderr}')
    if name.startswith('math:'):
        require('fixture mismatch' not in completed.stderr and 'integrity mismatch' not in completed.stderr,
                f'generic integrity failure for {name}')
    print(f'PASS: {name} -> {expected}')

def fault_probes(optimized):
    source = (ROOT/'check.py').read_text()
    with tempfile.TemporaryDirectory(prefix='report110_auditor_') as temporary:
        copy = Path(temporary)
        shutil.copytree(ROOT/'data', copy/'data')
        for name, old, new, expected in MUTATIONS:
            require(old in source, f'mutation anchor missing: {name}')
            (copy/'check.py').write_text(source.replace(old,new))
            expect_failure(copy, optimized, 'math:'+name, expected)
        (copy/'check.py').write_text(source)
        fixture = copy/'data'/'counts.json'
        original = fixture.read_bytes()
        data = json.loads(original)
        data['0'][1][1] += 1
        fixture.write_text(json.dumps(data))
        expect_failure(copy, optimized, 'fixture:value', 'fixture mismatch counts.json')
        fixture.write_text('{"0":[],"0":[]}')
        expect_failure(copy, optimized, 'fixture:duplicate_key', 'duplicate fixture key')
        fixture.write_text('{')
        expect_failure(copy, optimized, 'fixture:invalid_json', 'invalid fixture counts.json')
        data = json.loads(original)
        data['0'][1][1] = True
        fixture.write_text(json.dumps(data))
        expect_failure(copy, optimized, 'fixture:boolean_for_integer', 'fixture mismatch counts.json')
        data = json.loads(original)
        data['0'][1][1] = 1.0
        fixture.write_text(json.dumps(data))
        expect_failure(copy, optimized, 'fixture:float_for_integer', 'fixture mismatch counts.json')
        fixture.unlink()
        expect_failure(copy, optimized, 'fixture:missing_file', 'fixture inventory')
        fixture.write_bytes(original)
        extra = copy/'data'/'extra.json'
        extra.write_text('{}')
        expect_failure(copy, optimized, 'fixture:extra_file', 'fixture inventory')
        extra.unlink()
        extra.mkdir()
        expect_failure(copy, optimized, 'fixture:extra_directory', 'fixture file type')
        extra.rmdir()
        fixture.unlink()
        outside = copy/'saved_counts.json'
        outside.write_bytes(original)
        fixture.symlink_to(outside)
        expect_failure(copy, optimized, 'fixture:symlink', 'fixture file type')
    return len(MUTATIONS) + 9

def main():
    before = snapshot()
    completed = execute(ROOT, bool(sys.flags.optimize))
    require(completed.returncode == 0, 'pristine checker failed: '+completed.stderr)
    comparisons = algebra_probes()
    faults = fault_probes(bool(sys.flags.optimize))
    require(snapshot() == before, 'pristine checker or fixture bytes changed')
    print(f'PASS: {comparisons} scalar series comparisons, PGF moments u=1..100, {faults} isolated faults')
    print('PASS: pristine checker and fixture hashes unchanged; optimized='+str(bool(sys.flags.optimize)))
    print(json.dumps(before, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
