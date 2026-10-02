"""Independent, source-pinned checks of the three incoming substrate reports.

The delivered archives stay unchanged. If a later intake retires them, read
their bytes from the tracked arrival commit. This checker is not a proof of
universality, a solver, or a substitute for the accompanying review.
"""
import argparse
from fractions import Fraction
import hashlib
import io
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import types
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[5]
ARRIVAL = '6914ccca6'
ARCHIVES = {
    'arithmetic_van_kampen.zip': 'c29f2918b5cddda37ca4a0190fbeba1930015c7d8e4a3fa55f13b5dd233e6ed9',
    'Infinite_Quantum_Runs_Diophantine_Certificates.zip': '9da3025f7f93c5f2a2f8c33b7b467f70c0c0ec22587a07cc1983d0615de90ff4',
    'three_commutative_phases_research.zip': '5a80275ba9811b77fdffa86524f10e5d7f88bf2fa39f6a386c46b1e875cf09c4',
}


def archive(name):
    assert type(name) is str and name in ARCHIVES
    path = ROOT / 'docs' / 'incoming' / name
    raw = (path.read_bytes() if path.exists() else subprocess.run(
        ['git', 'show', f'{ARRIVAL}:docs/incoming/{name}'], cwd=ROOT,
        check=True, capture_output=True).stdout)
    assert hashlib.sha256(raw).hexdigest() == ARCHIVES[name]
    with ZipFile(io.BytesIO(raw)) as z:
        assert len(z.namelist()) == len(set(z.namelist()))
        return {n: z.read(n) for n in z.namelist()}


def module(files, member, name):
    # Only exact bytes from a hash-checked tracked archive reach execution.
    m = types.ModuleType(name)
    m.__file__ = member
    sys.modules[name] = m
    exec(compile(files[member], member, 'exec'), m.__dict__)
    return m


def mm(a, b):
    assert a and b and len(a[0]) == len(b)
    assert all(len(r) == len(a[0]) for r in a)
    assert all(len(r) == len(b[0]) for r in b)
    return tuple(tuple(sum(x*y for x, y in zip(row, col))
                       for col in zip(*b)) for row in a)


def madd(a, b, sign=1):
    assert len(a) == len(b) and all(len(x) == len(y) for x, y in zip(a, b))
    return tuple(tuple(x+sign*y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def heisenberg_matrix(t):
    a, b, c = t
    return ((1, a, c), (0, 1, b), (0, 0, 1))


def heisenberg_checks(files):
    h = module(files, 'three_commutative_phases/code/heisenberg_compiler.py',
               '_incoming_review_heisenberg')
    rng = random.Random(6914)
    counts = dict(normal_forms=0, canonical_products=0, offzero_quartics=0,
                  within_phase_commutations=0)
    for n in (1, 2, 3, 4):
        for _ in range(4):
            rows = [h.QuadraticRow(rng.randint(-3, 3),
                tuple(rng.randint(-3, 3) for _ in range(n)),
                tuple(rng.randint(-3, 3) for _ in range(n)),
                tuple((i, j, rng.randint(-3, 3)) for i in range(n) for j in range(i+1, n)))
                for _ in range(3)]
            compiled = h.compile_quadratics(n, rows)
            bases = compiled.bases()
            for basis in bases:
                for a, b in itertools.combinations(basis, 2):
                    for ac, bc in zip(a.h, b.h):
                        assert mm(heisenberg_matrix(ac), heisenberg_matrix(bc)) == mm(
                            heisenberg_matrix(bc), heisenberg_matrix(ac))
                    counts['within_phase_commutations'] += 1
            for _ in range(32):
                x = tuple(rng.randint(-5, 5) for _ in range(n))
                lx = tuple(sum(a*b for a, b in zip(r, x)) for r in compiled.L)
                binom = tuple(a*(a-1)//2 for a in lx)
                normal = tuple(c+sum(d*v for d, v in zip(ds, x))+
                    sum(a*b for a, b in zip(cs, binom))
                    for c, ds, cs in zip(compiled.c, compiled.D, compiled.C))
                # Evaluate the original supplied quadratic coefficients directly.
                raw = tuple(r.constant+sum(a*b for a, b in zip(r.linear, x))+
                    sum(a*b*b for a, b in zip(r.diagonal, x))+
                    sum(c*x[i]*x[j] for i, j, c in r.cross) for r in rows)
                assert raw == normal
                counts['normal_forms'] += 1
                aa, bb, tt = compiled.canonical(x)
                for ac, bc, tc in zip(aa.h, bb.h, tt.h):
                    assert mm(mm(heisenberg_matrix(ac), heisenberg_matrix(bc)),
                              heisenberg_matrix(tc)) == ((1, 0, 0), (0, 1, 0), (0, 0, 1))
                assert tuple(v+c for v, c in zip(aa.z, compiled.c)) == raw
                counts['canonical_products'] += 1
                y = tuple(rng.randint(-3, 3) for _ in range(n))
                u = tuple(rng.randint(-3, 3) for _ in range(compiled.N))
                r = tuple(rng.randint(-3, 3) for _ in range(compiled.N))
                target = tuple(rng.randint(-3, 3) for _ in rows)
                phases = (compiled.phase_a(x, u), compiled.phase_b(y), compiled.phase_t(r))
                value = 0
                for ac, bc, tc in zip(*(p.h for p in phases)):
                    m = mm(mm(heisenberg_matrix(ac), heisenberg_matrix(bc)), heisenberg_matrix(tc))
                    value += m[0][1]**2+m[1][2]**2+4*m[0][2]**2
                value += sum((sum(p.z[j] for p in phases)-target[j]+compiled.c[j])**2
                             for j in range(compiled.m))
                assert value == compiled.quartic(target, x, u, y, r)
                counts['offzero_quartics'] += 1
    linear = [1]
    row = h.QuadraticRow(0, linear, [0])
    compiled = h.compile_quadratics(1, [row])
    linear[0] = 2
    assert compiled.evaluate([1]) == (2,)
    a, b, t = compiled.canonical([1])
    assert a*b*t == compiled.target([1])
    assert a*b*t != compiled.target([2])
    counts['mutable_constructor_counterexample'] = dict(
        input=1, mutated_evaluate=2, compiled_factorization_target=1,
        scope='Accepted mutable Python constructor input; JSON loading snapshots tuples and is unaffected.')
    return counts


def van_kampen_checks(files):
    v = module(files, 'arithmetic_van_kampen/code/van_kampen.py', '_incoming_review_van_kampen')
    word = 'ab'*30
    nodes = [v.Node('leaf', word=word),
             v.Node('fixed_conjugate', (0,), matrix=(1.0, 0.0, 0.0, 1.0))]
    system = v.compile_dag(nodes, [word])
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp)/'export.json'
        system.export(path)
        exported = json.loads(path.read_text())
    assert exported['variables'] == []
    boundary = [-dict((tuple(e), c) for e, c in r)[(0, 0, 0, 0)]
                for r in exported['residuals']]
    for residual in exported['residuals']:
        total = 0
        for exponents, coefficient in residual:
            assert type(coefficient) is int
            for x, e in zip(boundary, exponents):
                coefficient *= x**e
            total += coefficient
        assert total == 0
    determinant = boundary[0]*boundary[3]-boundary[1]*boundary[2]
    assert determinant == -69402857361589764505112412160
    assert v.det(v.evaluate_word(word)) == 1
    empty = v.budget_residuals(['abAB'], v.BudgetWitness([], [], [], [], ()))
    assert empty == []
    return dict(float_input_false_zero=boundary, false_zero_determinant=determinant,
                exported_residuals=4, true_relator=list(v.evaluate_word(word)),
                malformed_empty_boundary_residuals=empty,
                scope='Reproduces defects of the delivered API, not failures on exact typed theorem inputs.')


def quantum_checks(files):
    checker = module(files, 'Infinite_Quantum_Runs/code/verify_certificate.py',
                     '_incoming_review_quantum_checker')
    exports = {}
    for name in ('scalar_geometric', 'partial_qubit', 'coherent_qubit',
                 'coherent_qubit_all_moments'):
        data = json.loads(files[f'Infinite_Quantum_Runs/examples/{name}_certificate.json'])
        exports[name] = checker.check(data)
    eye = ((1, 0), (0, 1)); zero = ((0, 0), (0, 0)); cases = 0
    matrices = [zero, eye, ((0, 0), (0, 1)), ((1, 1), (0, 0)),
                ((0, 1), (0, 0)), ((1, 2), (0, 1)),
                ((0, 0), (0, Fraction(1, 2)))]
    zeros = 0
    for a in matrices:
        for gs in itertools.product((-2, -1, 0, 1, 2), repeat=4):
            g = (gs[:2], gs[2:]); p = madd(eye, mm(a, g), -1)
            three = mm(a, p) == zero and mm(p, g) == zero
            four = mm(g, a) == madd(eye, p, -1) and mm(a, p) == zero and mm(g, p) == zero
            assert three == four
            cases += 1; zeros += three
    # A wrong one-sided deletion leaves the upper-right entry free.
    a = ((0, 0), (0, 1)); g = ((0, 1), (0, 1)); p = ((1, 0), (0, 0))
    assert madd(mm(a, g), p) == eye and mm(a, p) == zero and mm(g, p) == zero
    assert mm(p, g) != zero and madd(mm(g, a), p) != eye
    return dict(original_exports=exports, independent_matrix_cases=cases,
                equal_zero_cases=zeros, reversed_product_counterexample=dict(A=a, G=g, P=p))


def verify():
    files = {name: archive(name) for name in ARCHIVES}
    return dict(status='PASS_INCOMING_SUBSTRATE_REVIEW_6914CCCA6', arrival=ARRIVAL,
        archives={n: dict(sha256=ARCHIVES[n], members={k: hashlib.sha256(v).hexdigest()
            for k, v in sorted(fs.items())}) for n, fs in files.items()},
        van_kampen=van_kampen_checks(files['arithmetic_van_kampen.zip']),
        heisenberg=heisenberg_checks(files['three_commutative_phases_research.zip']),
        quantum=quantum_checks(files['Infinite_Quantum_Runs_Diophantine_Certificates.zip']),
        scope='Finite independent checks, reviewed proofs, and reproduced API defects; no universal operation bound or formal verification.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == json.loads(json.dumps(result)), 'receipt mismatch'
    print(result['status'])
    print(json.dumps({k: v for k, v in result.items() if k not in ('archives', 'quantum')}, indent=2))
