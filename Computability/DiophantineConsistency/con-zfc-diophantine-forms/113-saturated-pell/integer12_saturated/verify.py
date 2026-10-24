#!/usr/bin/env python3
"""Independent exact checks for the saturated twelve-integer polynomials.

No candidate producer is imported. Every displayed polynomial register is
checked in a free local polynomial ring, the complete norm is reconstructed
by successively multiplying conjugates, and the attained degree follows by
an exact leading induction with a separately proved cancellation identity.
These finite certificates do not replace the ordinary arithmetic proof.
"""
import argparse
import ast
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import gzip
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 't', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']

# Independent mathematical transcription. Association and factorization
# deliberately differ from the arithmetic schedule in the producer.
FORMULAS = [
    ('J', '6*j+1'), ('qm', 'beta*J'), ('q', 'beta*J+1'),
    ('W0', '4*(3*w+1)'), ('X', 'q*W0'), ('Y', '(2*v+1)*q*q*q'),
    ('a', '(X+1)*Y'), ('H', '4*a+3'), ('Delta', '(a+2)*(a+2)-1'),
    ('F', '(K0+W0)*C-z*qm'),
    ('R', '(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
    ('k', 'R+1+h*X*Y'), ('eta', 'c-Y*k'), ('zeta', '(Y+1)*k-c'),
    ('coneU', 'cone_A*F'), ('coneV', 'cone_B*C'),
    ('G', 'coneU*coneV-(q-coneU-coneV)*(q-coneU-coneV)'),
    ('Peta', 'eta*zeta'), ('err', 't*t-G-Peta+1'),
    ('Pair', 'G*Peta-err*err'), ('Dg81', '81*((3*Pair-4)*s*s+1)'),
    ('ell', 'X*Y*Y'), ('Dt', '1+ell*(ell+1)*k*k'),
    ('U', 's*r*c*c'), ('Df', '1+Delta*U*U*Dt'),
    ('Q', 'Delta*Delta*U*U*Dt'), ('delta', 'Q-1'),
    ('b', 'c-R+4*U*Dt*T'), ('V', 'Df*b-c'), ('Cy', 'Q*V*V-1'),
    ('K', 'X*X+2*X*a*c-1'), ('S', 'U*H*H*H*H*H'),
    ('zc', 'H*T+K'),
    ('Ac', '(zc*zc+3*H*H)*(zc*zc*zc-19*H*H*H)'),
    ('G2', 'Dt*Df')]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load(name):
    return json.loads((HERE / name).read_bytes())


def local_evaluate(packet, target, bindings, oracle, covered=None):
    nodes = packet['nodes']
    cache = dict(bindings)

    def at(i):
        if covered is not None:
            covered.add(i)
        if i in cache:
            return cache[i]
        row = nodes[i]
        if row[0] == 'integer':
            val = oracle.Poly(row[1])
        else:
            need(row[0] in ('add', 'sub', 'mul'), 'local cut binds every leaf ' + str(row))
            a, b = at(row[1]), at(row[2])
            val = a+b if row[0] == 'add' else a-b if row[0] == 'sub' else a*b
        cache[i] = val
        return val
    return at(target)


def prefix(packet, oracle, integral):
    names = packet['named_registers']
    formulas = list(FORMULAS)
    formulas += [('center', 'S*(n+delta*V)-Ac' if integral else 'S*(n+V)-Ac'),
                 ('fs', 'center*center' if integral else 'delta*center*center'),
                 ('fc', 'S*S*delta*Cy' if integral else 'S*S*Cy'),
                 ('fa', '9*S*S*G2' if integral else '9*delta*S*S*G2'),
                 ('fb', 'S*S*Dg81' if integral else 'delta*S*S*Dg81')]
    covered, proofs = set(), []
    for name, text in formulas:
        tree = ast.parse(text, mode='eval').body
        refs = sorted({n.id for n in ast.walk(tree) if isinstance(n, ast.Name)})
        need(len(refs) <= 6, 'six-port free polynomial cut')
        symbols = {v: oracle.variable(j) for j, v in enumerate(refs)}
        bindings = {names[v]: symbols[v] for v in refs}

        def expected(n):
            if isinstance(n, ast.Name):
                return symbols[n.id]
            if isinstance(n, ast.Constant):
                return oracle.Poly(n.value)
            need(isinstance(n, ast.BinOp), 'polynomial mathematical formula')
            a, b = expected(n.left), expected(n.right)
            return a+b if isinstance(n.op, ast.Add) else a-b if isinstance(n.op, ast.Sub) else a*b

        actual = local_evaluate(packet, names[name], bindings, oracle, covered)
        need(actual.t == expected(tree).t, 'entire polynomial register ' + name)
        proofs.append({'register': name, 'free_cuts': refs})
    missing = [i for i in range(names['sum'])
               if packet['nodes'][i][0] in ('add', 'sub', 'mul') and i not in covered]
    need(not missing, 'every live prefix arithmetic gate covered ' + str(missing))
    return {'complete_local_ring_cuts': proofs, 'prefix_arithmetic_covered': True}


def full_norm(packet, oracle):
    names = packet['named_registers']
    x, a, b, c = [oracle.variable(i) for i in range(4)]
    bindings = {names['fs']: x*x, names['fa']: a, names['fb']: b, names['fc']: c}
    actual = local_evaluate(packet, packet['output'], bindings, oracle)
    expected = oracle.norm_oracle(x, [a, b, c])
    need(actual.t == expected.t and len(expected.t) == 35,
         'all 35 coefficients of the full eight-conjugate norm')
    s, a, b, c = [oracle.variable(i) for i in range(4)]
    bindings = {names['fs']: s, names['fa']: a, names['fb']: b, names['fc']: c}
    omega = s-c
    expected_pe = omega*omega-2*(a+b)*(2*c+omega)+(a-b)*(a-b)
    actual_pe = local_evaluate(packet, names['Pe'], bindings, oracle)
    need(actual_pe.t == expected_pe.t, 'literal Pe cancellation identity')
    return {'full_norm_coefficients': len(expected.t), 'all_norm_cuts_bound': True,
            'literal_Pe_identity_checked': True}


def symbolic_identities(oracle, integral):
    d, S, V, z = [oracle.variable(i) for i in range(4)]
    if integral:
        actual = (S*d*V+z)**2-S*S*d*((d+1)*V*V-1)
        expected = z*z+2*S*d*V*z-S*S*d*V*V+S*S*d
    else:
        actual = d*(S*V+z)**2-S*S*((d+1)*V*V-1)
        expected = d*z*z+2*d*S*V*z-S*S*(V*V-1)
    need(actual.t == expected.t, 'entire centered omega identity')
    omega_terms = len(expected.t)
    Delta, U, tau, E, T = [oracle.variable(i) for i in range(5)]
    identities = [
        ((1+Delta*(U*tau)**2)-(1+Delta*U*U*E), Delta*U*U*(tau*tau-E)),
        ((Delta*U*tau)**2-Delta*Delta*U*U*E, Delta*Delta*U*U*(tau*tau-E)),
        (4*(U*tau)*(tau*T)-4*U*E*T, 4*U*T*(tau*tau-E))]
    for actual, expected in identities:
        need(actual.t == expected.t, 'exact strong/auxiliary restoration identity')
    return {'centered_omega_identity_terms': omega_terms,
            'all_three_restoration_identities': True}


def topology(packet, integral):
    nodes = packet['nodes']
    degrees = []
    for i, row in enumerate(nodes):
        if row[0] in ('add', 'sub', 'mul'):
            need(len(row) == 3 and all(type(j) is int and 0 <= j < i for j in row[1:]),
                 'acyclic ordinary binary arithmetic')
            da, db = (degrees[j] for j in row[1:])
            degree = da+db if row[0] == 'mul' else max(da, db)
        else:
            need(row[0] in ('variable', 'coefficient', 'integer'), 'only polynomial nodes')
            degree = int(row[0] == 'variable')
        degrees.append(degree)
    live, todo = set(), [packet['output']]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        if nodes[i][0] in ('add', 'sub', 'mul'):
            todo.extend(nodes[i][1:])
    need(live == set(range(len(nodes))), 'complete circuit liveness')
    need([r[1] for r in nodes if r[0] == 'variable'] == VARS, 'all twelve variables')
    need([r[1] for r in nodes if r[0] == 'coefficient'] == PORTS, 'all six coefficient ports')
    counts = dict(Counter(r[0] for r in nodes if r[0] in ('add', 'sub', 'mul')))
    need(counts == packet['operation_counts'] == {'mul': 75, 'add': 25, 'sub': 23},
         'literal operation census')
    need(sum(counts.values()) == packet['operations'] == 123, 'complete 123-operation count')
    need(degrees[packet['output']] == packet['syntactic_bound'] == (1544 if integral else 1280),
         'syntactic degree bound')
    return {'nodes': len(nodes), 'operations': 123, 'operation_counts': counts,
            'syntactic_degree': degrees[packet['output']]}


def leading(packet, oracle, integral):
    """Every gate's leading monomial, with the proven Pe cut at cancellation."""
    names = packet['named_registers']
    order = ['T', 'j', 'w', 'v', 's', 'r', 'c', 'h', 'C', 'z', 'n', 't']
    values = []

    def key(v):
        return (sum(v[0]),)+v[0]

    def times(a, b):
        return (tuple(x+y for x, y in zip(a[0], b[0])), a[1]*b[1])

    def scale(a, c):
        return (a[0], c*a[1])

    def value(name):
        return values[names[name]]

    for i, row in enumerate(packet['nodes']):
        if i == names['Pe']:
            expected_degrees = {'S': 34, 'V': 93, 'delta': 66, 'Ac': 45,
                                'Dt': 34, 'Df': 54, 'Dg81': 46,
                                'fa': 156 if integral else 222,
                                'fb': 114 if integral else 180,
                                'fc': 386 if integral else 320,
                                'fs': 386 if integral else 320}
            for name, deg in expected_degrees.items():
                need(sum(value(name)[0]) == deg, 'prefix attained degree ' + name)
            # z0=Sn-Ac has degree45. In the centered omega identity,
            # the unique maximum is -S^2 V^2 (rational) or -S^2 delta V^2.
            if integral:
                need(320 > max(90, 238, 134), 'unique integral omega top')
                top = times(times(value('S'), value('S')),
                            times(value('delta'), times(value('V'), value('V'))))
                v = times(top, top)
                need(640 > max(542, 500, 476, 434, 312, 270, 228), 'unique integral Pe top')
            else:
                need(254 > max(156, 238, 68), 'unique rational omega top')
                v = scale(times(value('fa'), value('fc')), -4)
                need(542 > max(508, 476, 500, 434, 444, 402, 360), 'unique rational Pe top')
        elif row[0] == 'variable':
            mon = [0]*12
            mon[order.index(row[1])] = 1
            v = (tuple(mon), oracle.Poly(1))
        elif row[0] == 'coefficient':
            v = ((0,)*12, oracle.variable(PORTS.index(row[1])))
        elif row[0] == 'integer':
            v = ((0,)*12, oracle.Poly(row[1]))
        else:
            a, b = values[row[1]], values[row[2]]
            if row[0] == 'mul':
                v = times(a, b)
            elif key(a) > key(b):
                v = a
            elif key(b) > key(a):
                v = scale(b, -1) if row[0] == 'sub' else b
            else:
                v = (a[0], a[1]-b[1] if row[0] == 'sub' else a[1]+b[1])
        need(bool(v[1].t), 'exact nonzero leading coefficient at gate ' + str(i))
        values.append(v)

    if integral:
        monomial = {'j': 728, 'w': 152, 'v': 192, 'h': 40,
                    's': 40, 'r': 40, 'c': 80, 'T': 8}
        powers, degree = (1320, 880, 728), 1280
    else:
        monomial = {'j': 624, 'w': 132, 'v': 164, 'h': 32,
                    's': 32, 'r': 32, 'c': 64, 'T': 4}
        powers, degree = (1144, 760, 624), 1084
    mon, coefficient = values[packet['output']]
    wanted = oracle.Poly(2**powers[0]*3**powers[1])*oracle.variable(0)**powers[2]
    need(mon == tuple(monomial.get(n, 0) for n in order) and coefficient.t == wanted.t,
         'actual whole-DAG attained leading coefficient')
    need(sum(mon) == degree == packet['exact_degree'], 'exact degree certificate')
    return {'exact_degree': degree, 'graded_lex_variable_order': order,
            'monomial': monomial, 'coefficient': '2^%d*3^%d*beta^%d' % powers,
            'all_nodes_exact_after_one_proved_cancellation': True}


def provenance_and_coefficients():
    pins = load('INHERITED_SOURCE_PINS.json')
    for path, digest in pins['retained_files'].items():
        need(sha256((HERE/path).read_bytes()).hexdigest() == digest, 'whole inherited file ' + path)
    binding = load('coefficients/BINDING.json')
    values, checked = {}, {}
    for name, pin in binding['payloads'].items():
        raw = gzip.decompress((HERE/'coefficients'/pin['file']).read_bytes())
        need(len(raw) == pin['raw_bytes'] and sha256(raw).hexdigest() == pin['raw_sha256'],
             'whole fixed integer bytes ' + name)
        values[name] = int.from_bytes(raw, 'little')
        need(values[name].bit_length() == pin['bits'], 'fixed integer width ' + name)
        checked[name] = {'bits': pin['bits'], 'raw_sha256': pin['raw_sha256']}
    need(values['beta'] == 2**1064921-1 and values['cone_A'] == 2**1113
         and values['cone_B'] == 2**666104, 'three explicit closed constants')
    recipe = module('saturated12_retained_source34_recipe', HERE/'coefficients/recipe/source34_builder.py')
    rebuilt, audit = recipe.construct()
    for name, old in [('beta', 'beta'), ('K0', 'K'), ('MC', 'MC'), ('MF', 'MF_source')]:
        need(values[name] == rebuilt[old], 'full native coefficient reconstruction ' + name)
    return {'whole_six_payloads': checked, 'full_recipe_reconstruction': audit,
            'retained_files_verified': len(pins['retained_files'])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    oracle = module('saturated12_independent_norm_oracle', HERE/'parent/source/independent_norm_oracle.py')
    provenance = provenance_and_coefficients()
    results, rejected = {}, []
    for integral in (False, True):
        variant = 'integral' if integral else 'rational'
        packet = load(variant+'.json')
        result = topology(packet, integral)
        result.update(prefix(packet, oracle, integral))
        result.update(full_norm(packet, oracle))
        result.update(symbolic_identities(oracle, integral))
        result['leading_certificate'] = leading(packet, oracle, integral)
        for target, checker in [
                ('b', lambda p: prefix(p, oracle, integral)),
                ('Df', lambda p: prefix(p, oracle, integral)),
                ('Dg81', lambda p: prefix(p, oracle, integral)),
                ('Ac', lambda p: prefix(p, oracle, integral)),
                ('output', lambda p: full_norm(p, oracle))]:
            bad = deepcopy(packet)
            row = bad['nodes'][bad['named_registers'][target]]
            row[0] = 'sub' if row[0] == 'add' else 'add'
            try:
                checker(bad)
            except ValueError:
                rejected.append(variant+':'+target)
            else:
                raise ValueError('corrupted mathematical polynomial accepted: '+target)
        results[variant] = result
    report = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
              'variants': results, 'provenance': provenance, 'rejected_mutations': rejected,
              'ordinary_proof_sha256': sha256((HERE/'PROOF.md').read_bytes()).hexdigest(),
              'scope': 'Complete local polynomial identities, all 35 free norm coefficients, '
                       'three source-restoration identities, exact cancellation and every-node '
                       'leading induction, complete fixed payload and recipe reconstruction. '
                       'The semantic reduction is the separately reviewed ordinary proof; no Lean claim.'}
    text = json.dumps(report, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
