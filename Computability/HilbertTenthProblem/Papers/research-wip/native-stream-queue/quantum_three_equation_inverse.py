"""A canonical three-equation group-inverse certificate from a pinned archive.

AG+P=I, AP=0, PG=0 uniquely specify the group inverse and projection whenever
zero is semisimple for A=I-T.  The PG order is essential.  Counts distinguish
rational circuit gates from natural coordinates and quadratic residuals;
integer-polynomial straight-line gate counts are not claimed.
"""
import argparse
from copy import deepcopy
from fractions import Fraction
from functools import lru_cache
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import zipfile

ROOT = Path(__file__).resolve().parents[5]
ARCHIVE = 'docs/incoming/Infinite_Quantum_Runs_Diophantine_Certificates.zip'
COMMIT = '6914ccca6'
ARCHIVE_SHA256 = '9da3025f7f93c5f2a2f8c33b7b467f70c0c0ec22587a07cc1983d0615de90ff4'
MEMBERS = {
    'quartic': ('Infinite_Quantum_Runs/code/quartic.py', '33991bd6d284ef935f2eee0b14db7a102beb613733dbf52ffd50232412e2c666'),
    'quantum_loops': ('Infinite_Quantum_Runs/code/quantum_loops.py', '1fa26c22f2ae6c16e5e701bcec58f83c6cd9c85f4611dc018f778be5d2fc9b63'),
    'verify_certificate': ('Infinite_Quantum_Runs/code/verify_certificate.py', '3a03bd538672918a79c1873507356e66b2f834405314e5347c58cd37669cc60f'),
}


def archive_bytes():
    path = ROOT/ARCHIVE
    blob = path.read_bytes() if path.is_file() else subprocess.run(
        ['git', 'show', COMMIT+':'+ARCHIVE], cwd=ROOT, check=True, capture_output=True).stdout
    assert hashlib.sha256(blob).hexdigest() == ARCHIVE_SHA256, 'pinned incoming archive changed'
    return blob


@lru_cache(None)
def _modules():
    result = {}
    with zipfile.ZipFile(io.BytesIO(archive_bytes())) as archive:
        for label, (member, digest) in MEMBERS.items():
            source = archive.read(member)
            assert hashlib.sha256(source).hexdigest() == digest
            name = '_three_equation_frozen_'+label
            module = types.ModuleType(name); module.__file__ = ARCHIVE+'!/'+member
            sys.modules[name] = module
            exec(compile(source, module.__file__, 'exec'), module.__dict__)
            result[label] = module
    return result


def exact_equal(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return (len(a) == len(b) and all(type(k) is str for k in a)
                and a.keys() == b.keys() and all(exact_equal(a[k], b[k]) for k in a))
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact_equal(x, y) for x, y in zip(a, b))
    return a == b


def input_key(t):
    assert type(t) is list and t and all(type(row) is list and len(row) == len(t) for row in t)
    assert all(type(x) is str and str(Fraction(x)) == x for row in t for x in row), 'canonical rational strings required'
    return tuple(tuple(row) for row in t)


def _three_core(t, g, p):
    """Use the actual frozen Circuit class, changing only the dense core recipe."""
    circuit = _modules()['quartic'].Circuit(); d = t.rows
    zero = circuit.rational('zero', 0, True); one = circuit.rational('one', 1, True)
    tw = circuit.matrix('T', t, True); gw = circuit.matrix('G', g); pw = circuit.matrix('P', p)
    aw = [[circuit.add(one if i == j else zero, tw[i][j], True) for j in range(d)] for i in range(d)]
    ag = circuit.matmul(aw, gw); ap = circuit.matmul(aw, pw); pg = circuit.matmul(pw, gw)
    for i in range(d):
        for j in range(d):
            circuit.equal(circuit.add(ag[i][j], pw[i][j]), one if i == j else zero)
            circuit.equal(ap[i][j], zero)
            circuit.equal(pg[i][j], zero)
    names = _modules()['quartic'].names
    metadata = dict(dimension=d, T=names(tw), G=names(gw), P=names(pw), core_statistics=circuit.stats())
    s = circuit.stats()
    assert s == dict(rational_wires=6*d**3+2*d*d+2, additions=3*d**3-d*d,
                     multiplications=3*d**3, equalities=4*d*d+2,
                     natural_variables=66*d**3+9*d*d+14, quadratic_residuals=54*d**3+6*d*d+10)
    return circuit, metadata


@lru_cache(None)
def _build(key):
    modules = _modules(); sp = modules['quantum_loops'].sp
    t = sp.Matrix([[sp.Rational(x) for x in row] for row in key])
    g, p = modules['quantum_loops'].group_inverse(t)
    circuit, metadata = _three_core(t, g, p)
    old, *_ = modules['quartic'].group_core(t, g, p)
    with tempfile.TemporaryDirectory(prefix='quantum-three-core-') as directory:
        data = circuit.export(Path(directory)/'certificate.json', metadata)
    data['three_equation_input'] = [list(row) for row in key]
    data['three_equation_contract'] = dict(
        equations=['AG+P=I', 'AP=0', 'PG=0'],
        witness_domain='nonnegative integers', canonical_wire=True,
        unique_rational_interface=['T', 'G', 'P'], unique_natural_witness=True,
        physical_validity='Not certified. The algebraic interface accepts exactly rational T with semisimple eigenvalue1 if present.',
        integer_polynomial_operations='Not counted; rational circuit gates and variable/residual counts only.',
        universal_bound='No universal computational relation or ordinary-input decoder is supplied.')
    data['provenance'] = dict(archive=ARCHIVE, archive_commit=COMMIT, archive_sha256=ARCHIVE_SHA256,
                             members={name: dict(path=path, sha256=digest) for name, (path, digest) in MEMBERS.items()})
    data['parent_statistics'] = old.stats()
    modules['verify_certificate'].check(data)
    assert all(type(c) is int and all(type(i) is int for i in indices)
               for residual in data['residuals'] for c, indices in residual)
    return data


def build(t=None):
    if t is None: t = [['9/25']]
    key = input_key(t); archive_bytes()
    return deepcopy(_build(key))


def checked(packet):
    assert type(packet) is dict
    key = input_key(packet.get('three_equation_input'))
    archive_bytes()
    assert exact_equal(packet, _build(key)), 'complete exact-type canonical three-equation packet required'


def polynomial_source(packet=None):
    """Return the full sparse quadratic residual list whose squared sum is Q."""
    if packet is None: packet = build()
    checked(packet)
    return deepcopy(packet['residuals'])


def evaluate(packet, values=None):
    checked(packet)
    if values is None: values = packet['witness']
    assert type(values) is list and len(values) == len(packet['variables'])
    assert all(type(v) is int and v >= 0 for v in values), 'natural integer assignment required'
    check = _modules()['verify_certificate']
    return sum(check.evaluate(r, values)**2 for r in packet['residuals'])


def export_certificate(packet, path):
    checked(packet)
    assert isinstance(path, (str, Path))
    Path(path).write_text(json.dumps(packet, separators=(',', ':'))+'\n')


def ledger(packet=None):
    if packet is None: packet = build()
    checked(packet)
    d = len(packet['three_equation_input']); new = packet['statistics']; old = packet['parent_statistics']
    assert old['additions']-new['additions'] == old['multiplications']-new['multiplications'] == d**3
    assert old['natural_variables']-new['natural_variables'] == 22*d**3
    assert old['quadratic_residuals']-new['quadratic_residuals'] == 18*d**3+d*d
    return dict(dimension=d, parent=old, successor=new, exact_degree=4,
                saved_rational_multiplications=d**3, saved_rational_additions=d**3,
                saved_natural_variables=22*d**3, saved_quadratic_residuals=18*d**3+d*d,
                integer_polynomial_gate_count=None)


def examples():
    analyzer = _modules()['quantum_loops']
    result = {'zero_continuation_d1': [['0']], 'identity_continuation_d1': [['1']],
              'nonsymmetric_index_one_d2': [['1', '-2'], ['0', '-1']],
              'invertible_A_jordan_d2': [['2', '1'], ['0', '2']]}
    for name in ('scalar_geometric', 'partial_qubit', 'coherent_qubit'):
        t = analyzer.example_data()[name]['T']
        result[name] = [[str(t[i, j]) for j in range(t.cols)] for i in range(t.rows)]
    return result


def algebra_audit():
    sp = _modules()['quantum_loops'].sp
    a = sp.diag(0, 1); p = sp.diag(1, 0); wrong = sp.Matrix([[0, 1], [0, 1]])
    assert a*wrong+p == sp.eye(2) and a*p == sp.zeros(2) and wrong*p == sp.zeros(2)
    assert p*wrong != sp.zeros(2) and wrong*a+p != sp.eye(2)
    rejected = 0
    for t in ([['1', '-1'], ['0', '1']], [['1', '-1', '0'], ['0', '1', '-1'], ['0', '0', '1']]):
        try: build(t)
        except ValueError: rejected += 1
        else: raise AssertionError('nonsemisimple zero accepted')
    return dict(wrong_GP_order_counterexample=dict(A=[[0, 0], [0, 1]], P=[[1, 0], [0, 0]], G=[[0, 1], [0, 1]]),
                wrong_GP_satisfies_three_old_equations=True, replacement_PG_rejects=True,
                index_greater_than_one_rejections=rejected)


def guards():
    rejected = 0
    def reject(fn):
        nonlocal rejected
        try: fn()
        except (AssertionError, ValueError, TypeError, KeyError, ZeroDivisionError): rejected += 1
        else: raise AssertionError('malformed caller accepted')
    for bad in ([], [[]], [[1]], [[True]], [[1.0]], [['1.0']], [['1/1']], [['-0']], [['01']],
                [['1/0']], [['1'], ['0']], (('1',),)):
        reject(lambda bad=bad: build(bad))
    p = build()
    for key, value in [('residuals', []), ('metadata', {}), ('parent_statistics', {}),
                       ('three_equation_contract', {}), ('provenance', {}), ('extra', True)]:
        for api in (checked, polynomial_source, evaluate, ledger):
            reject(lambda key=key, value=value, api=api: api(dict(p, **{key: value})))
    for value in (1.0, True):
        bad = deepcopy(p); r = next(r for r in bad['residuals'] if any(c == 1 for c, ids in r))
        term = next(term for term in r if term[0] == 1); term[0] = value
        for api in (checked, polynomial_source, evaluate, ledger): reject(lambda api=api: api(bad))
        bad = deepcopy(p); term = next(term for r in bad['residuals'] for term in r if term[1]); term[1][0] = value
        reject(lambda: checked(bad))
        values = list(p['witness']); values[0] = value; reject(lambda: evaluate(p, values))
    for values in ([], tuple(p['witness']), [-1]*len(p['witness'])): reject(lambda values=values: evaluate(p, values))
    # A public return never aliases the private canonical guard, including before
    # any successor request can use a damaged returned reference.
    _build.cache_clear()
    first = build([['1']]); first['residuals'].clear(); first['metadata']['T'].clear()
    reject(lambda: checked(first))
    second = build([['1']]); assert second['residuals'] and second['metadata']['T'] == [['T[0,0]']]
    return rejected


def verify():
    forms = []; mutation_count = 0
    for name, t in examples().items():
        packet = build(t); report = _modules()['verify_certificate'].check(packet)
        assert evaluate(packet) == 0
        # Each supplied natural coordinate is incident to an actual residual.
        incident = [[] for _ in packet['witness']]
        for residual in packet['residuals']:
            for i in {i for c, indices in residual for i in indices}: incident[i].append(residual)
        values = list(packet['witness']); raw = _modules()['verify_certificate'].evaluate
        for i in range(len(values)):
            values[i] += 1
            assert any(raw(r, values) != 0 for r in incident[i])
            values[i] -= 1; mutation_count += 1
        with tempfile.TemporaryDirectory(prefix='quantum-three-export-') as directory:
            path = Path(directory)/'out.json'; export_certificate(packet, path)
            decoded = json.loads(path.read_text()); assert exact_equal(packet, decoded)
            assert _modules()['verify_certificate'].check(decoded) == report
        forms.append(dict(name=name, input=t, ledger=ledger(packet), independent_check=report,
                          certificate_sha256=hashlib.sha256(json.dumps(packet, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
                          certificate=packet))
    return dict(status='PASS_QUANTUM_THREE_EQUATION_INVERSE',
                source_file_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                archive_sha256=ARCHIVE_SHA256, forms=forms, algebra=algebra_audit(),
                one_coordinate_mutation_rejections=mutation_count, malformed_call_rejections=guards(),
                scope='Canonical unique natural inverse-core witnesses via the same rational T,G,P interface. Physical validity, full moment compilers and integer-polynomial gate counts are not supplied by this wrapper.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = verify(); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print({k: v for k, v in result.items() if k not in ('status', 'forms')})
