#!/usr/bin/env python3
"""Exact finite checks, independent of the producer's arithmetic formulas.

Uses the credited sparse-polynomial primitive but independently transcribes
the complete mathematics. Ordinary semantic proofs are in PROOF.md and
the retained sources; finite checks do not replace those proofs.
"""
import ast
import gzip
import hashlib
import importlib.util
import itertools
import json
from collections import Counter
from pathlib import Path
from exact_polynomial import Ring

ROOT = Path(__file__).resolve().parent
NAMES = ['powered_coprime11_direct', 'powered_coprime11_aux']
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']


def need(ok, message):
    if not ok:
        raise ValueError(message)


def formulas(centered):
    rows = [
        ('J', '6*j+1'), ('qm', 'beta*J'), ('q', 'qm+1'),
        ('q2', 'q*q'), ('q3', 'q*q*q'), ('W', '12*w+4'),
        ('X', 'q*W'), ('Y', '(2*v+1)*q*q*q'), ('E', 'X*Y'),
        ('a', '(X+1)*Y'), ('H', '4*a+3'), ('Delta', 'a*a+H'),
        ('F', '(K0+W)*C-z*qm'),
        ('R', '(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
        ('k', 'R+1+h*E'), ('c2', 'c*c'), ('eta', 'c-Y*k'),
        ('U', 'cone_A*F'), ('Vc', 'cone_B*C'),
        ('Derr', '(U-q)**2+(Vc-q)**2'),
        ('Budget', 'k*k*(q*q-Derr)-4*q*q*eta*eta'),
        ('ell', 'X*Y*Y'), ('L', 'ell*k'),
        ('Dt', '1+ell*(ell+1)*k*k'), ('D', '3*Budget-4'),
        ('Dg', '1+D*Dt*s*s'), ('I', '2*r*c*c'), ('I2', 'I*I'),
        ('strong', 'Delta*I*I'), ('Df', '1+Delta*I*I'),
        ('Q', 'Delta*Delta*I*I'), ('delta', 'Q-1'),
        ('bfront', 'c-R+4*I*T'), ('V', 'Df*bfront-c'),
        ('Cy', 'Q*V*V-1'), ('Da', '(Q-1)*(Q*V*V-1)'),
        ('K', 'X*(3*c-2*X)+2'), ('H2', 'H*H'), ('H3', 'H*H*H'),
        ('S', 's*r*H'), ('S2', 'S*S'), ('zc', 'H*T+K'),
        ('zc2', 'zc*zc'),
        ('Ac', '(zc*zc+3*H*H)*(zc*zc*zc-19*H*H*H)')]
    if centered:
        rows += [('shift', 'Q*V'), ('Z', 'S*(n+shift)-Ac')]
    else:
        rows += [('Z', 'S*n-Ac')]
    rows += [
        ('P', 'Dt*Dg'), ('u', '4*S*S*Df'), ('b', 'S*S*Da'),
        ('e', '16*S*S*P'), ('Z2', 'Z*Z'), ('ub_sum', 'u+b'),
        ('ub_product', 'u*b'), ('vnorm', 'Z*Z-u-b-e'),
        ('ynorm', 'vnorm*vnorm-4*(u*b+u*e+b*e)'),
        ('output', 'ynorm*ynorm-64*u*b*e*Z*Z')]
    return rows


def local_checks(packet):
    nodes = packet['nodes']
    names = dict(packet['named_registers'])
    names.update({row[1]: i for i, row in enumerate(nodes)
                  if row[0] in ('variable', 'coefficient')})
    names['output'] = packet['output']
    covered = set()
    ledger = []
    for name, expression in formulas(packet['centered']):
        need(name in names, 'missing mathematical register '+name)
        tree = ast.parse(expression, mode='eval')
        refs = sorted({node.id for node in ast.walk(tree) if isinstance(node, ast.Name)})
        ring = Ring(refs)
        environment = {ref: ring.var(ref) for ref in refs}
        memo = {names[ref]: value for ref, value in environment.items()}

        def evaluate(index):
            covered.add(index)
            if index in memo:
                return memo[index]
            row = nodes[index]
            if row[0] == 'integer':
                value = ring.scalar(row[1])
            else:
                need(row[0] in ('add', 'sub', 'mul'), 'unbound local leaf '+str(row))
                left, right = evaluate(row[1]), evaluate(row[2])
                value = left+right if row[0] == 'add' else left-right if row[0] == 'sub' else left*right
            memo[index] = value
            return value

        expected = eval(expression, {'__builtins__': {}}, environment)
        need(evaluate(names[name]).terms == expected.terms, 'free-ring identity '+name)
        ledger.append({'register': name, 'expression': expression, 'free_inputs': refs})
    missing = [i for i, row in enumerate(nodes)
               if row[0] in ('add', 'sub', 'mul') and i not in covered]
    need(not missing, 'all live arithmetic covered '+str(missing))
    return ledger


def universal():
    ring = Ring(['z', 'u', 'b', 'e'])
    z, u, b, e = [ring.var(n) for n in ring.names]
    radicands = [u, b, e]
    product = {0: ring.scalar(1)}
    for signs in itertools.product([-1, 1], repeat=3):
        factor = {0: z, 1: -signs[0]*ring.scalar(1),
                  2: -signs[1]*ring.scalar(1), 4: -signs[2]*ring.scalar(1)}
        new = {}
        for left, x in product.items():
            for right, y in factor.items():
                value = x*y
                for bit, radicand in enumerate(radicands):
                    if (left & right) & (1 << bit):
                        value = value*radicand
                key = left ^ right
                new[key] = new.get(key, ring.scalar(0))+value
        product = {key: value for key, value in new.items() if value.terms}
    expected = ((z*z-u-b-e)**2-4*(u*b+u*e+b*e))**2-64*u*b*e*z*z
    need(set(product) == {0} and product[0].terms == expected.terms, 'all eight conjugates')
    need(len(expected.terms) == 35, 'all 35 generic coefficients')
    ring = Ring(['X', 'a', 'c', 'S', 'Q', 'V', 'B'])
    X, a, c, S, Q, V, B = [ring.var(n) for n in ring.names]
    need(((4*a+3)*X*c-2*(X*(X+2*a*c)-1)-(X*(3*c-2*X)+2)).terms == {}, 'short projection identity')
    need((S*S*(Q-1)*(Q*V*V-1)-(S*Q*V)**2+S*S*(Q*(V*V+1)-1)).terms == {}, 'new center identity')
    need(((B+S*Q*V)**2-S*S*(Q-1)*(Q*V*V-1)
          -(B*B+2*S*Q*V*B+S*S*(Q*(V*V+1)-1))).terms == {}, 'degree-revealing omega identity')
    return {'norm_coefficients': 35, 'eight_conjugates': True,
            'short_projection_identity': True, 'center_identity': True,
            'degree_revealing_identity': True}


def degree_certificate(centered):
    # Every abbreviation here is an independently transcribed top homogeneous
    # form. Including both terms of R checks an actual fixed-coefficient slice.
    ring = Ring(['C', 'j', 'w', 'v', 'h', 's', 'r', 'c', 'T', 'z', 'n', 'beta'])
    C, j, w, v, h, s, r, c, T, z, n, beta = [ring.var(x) for x in ring.names]
    q = 6*beta*j
    Y = 2*v*q**3
    a = q*(12*w)*Y
    R = -q**3*(12*w*C-q*z)
    k = h*a
    Dt = (a*Y*k)**2
    budget = -4*q*q*Y*Y*k*k
    Dg = 3*budget*Dt*s*s
    P = Dt*Dg
    I = 2*r*c*c
    S = 4*s*r*a
    Q = a**4*I*I
    V = -a*a*I*I*R
    b = S*S*Q*Q*V*V
    e = 16*S*S*P
    top = 16*b*b*e*e if centered else b**4
    degree = 464 if centered else 488
    need(all(sum(m[:-1]) == degree for m in top.terms), 'homogeneous leading form')
    monomial = max(top.terms, key=lambda m: m[:-1])
    coefficient = top.terms[monomial]
    need(coefficient > 0, 'positive selected leading coefficient')
    residue = coefficient
    factors = {}
    for prime in [2, 3]:
        power = 0
        while residue % prime == 0:
            power += 1
            residue //= prime
        factors[str(prime)] = power
    need(residue == 1, 'selected coefficient is a 2,3 monomial')
    factors['beta'] = monomial[-1]
    expected = {'2': 484, '3': 318, 'beta': 260} if centered else {'2': 480, '3': 312, 'beta': 248}
    need(factors == expected, 'independent explicit coefficient calculation')
    return {'exact_degree': degree, 'monomial': dict(zip(ring.names[:-1], monomial[:-1])),
            'coefficient_factors': factors, 'leading_form_terms': len(top.terms),
            'nonzero_for_authentic_beta': True,
            'leading_form': '16*b_top^2*e_top^2' if centered else 'b_top^4'}


def topology(packet):
    nodes = packet['nodes']
    degrees = []
    for i, row in enumerate(nodes):
        if row[0] in ('add', 'sub', 'mul'):
            need(len(row) == 3 and all(type(j) == int and 0 <= j < i for j in row[1:]), 'acyclic binary gate')
            degrees.append(degrees[row[1]]+degrees[row[2]] if row[0] == 'mul' else max(degrees[row[1]], degrees[row[2]]))
        else:
            need(row[0] in ('variable', 'coefficient', 'integer'), 'leaf kind')
            degrees.append(int(row[0] == 'variable'))
    live = set()
    queue = [packet['output']]
    while queue:
        i = queue.pop()
        if i in live:
            continue
        live.add(i)
        if nodes[i][0] in ('add', 'sub', 'mul'):
            queue.extend(nodes[i][1:])
    need(live == set(range(len(nodes))), 'no dead nodes')
    need([r[1] for r in nodes if r[0] == 'variable'] == VARS, 'exact eleven variables')
    need([r[1] for r in nodes if r[0] == 'coefficient'] == PORTS, 'exact six fixed ports')
    count = Counter(row[0] for row in nodes if row[0] in ('add', 'sub', 'mul'))
    need(dict(count) == packet['operation_counts'] and sum(count.values()) == packet['operations'], 'exact operation count')
    need(packet['operations'] == (122 if packet['centered'] else 121), 'selected operation count')
    need(degrees[packet['output']] == packet['syntactic_degree_bound'] == 488, 'naive syntactic bound')
    wanted = {'S': 8, 'Df': 18, 'Q': 30, 'V': 23, 'Cy': 76, 'Da': 106,
              'Dg': 60, 'Dt': 34, 'P': 94, 'Ac': 35, 'u': 34, 'b': 122, 'e': 110}
    for name, degree in wanted.items():
        need(degrees[packet['named_registers'][name]] == degree, 'prefix degree '+name)
    return {'live_nodes': len(nodes), 'operations': sum(count.values()), 'counts': dict(count), 'naive_degree_bound': 488}


def actual_leading(packet, certificate):
    # Degree-lex induction on every live node. The sole canceled upper bound
    # is replaced using the exact omega identity checked above, at the precise
    # matching node. This proves an upper bound and an attained coefficient.
    order = ['C', 'j', 'w', 'v', 'h', 's', 'r', 'c', 'T', 'z', 'n']
    cr = Ring(PORTS)
    zero = (0,)*len(order)
    values = []
    names = packet['named_registers']
    def key(x):
        return (sum(x[0]),)+x[0]
    def multiply(x, y):
        return tuple(a+b for a, b in zip(x[0], y[0])), x[1]*y[1]
    def add(x, y, subtract=False):
        if key(x) > key(y):
            return x
        if key(x) < key(y):
            return y[0], -y[1] if subtract else y[1]
        return x[0], x[1]-y[1] if subtract else x[1]+y[1]
    override = None
    if packet['centered']:
        row = packet['nodes'][names['vnorm']]
        need(row[0] == 'sub' and row[2] == names['e'], 'exact centered finalizer schedule')
        override = row[1]
    for i, row in enumerate(packet['nodes']):
        if i == override:
            need(row == ['sub', names['Z2'], names['ub_sum']], 'exact canceled node')
            n_index = next(j for j, r in enumerate(packet['nodes']) if r == ['variable', 'n'])
            C0 = multiply(values[names['S']], values[names['shift']])
            B0 = add(multiply(values[names['S']], values[n_index]), values[names['Ac']], True)
            value = multiply((zero, cr.scalar(2)), multiply(C0, B0))
            need(sum(value[0]) == 96, 'omega-minus-u attained degree')
            # Other exact omega terms have degrees 70 and 92; deg(u)=34.
        elif row[0] == 'variable':
            exponents = [0]*len(order)
            exponents[order.index(row[1])] = 1
            value = tuple(exponents), cr.scalar(1)
        elif row[0] == 'coefficient':
            value = zero, cr.var(row[1])
        elif row[0] == 'integer':
            value = zero, cr.scalar(row[1])
        else:
            left, right = values[row[1]], values[row[2]]
            value = multiply(left, right) if row[0] == 'mul' else add(left, right, row[0] == 'sub')
        need(bool(value[1].terms), 'nonzero exact leading coefficient at node '+str(i))
        values.append(value)
    final = values[packet['output']]
    need(dict(zip(order, final[0])) == certificate['monomial'], 'actual DAG leading monomial')
    f = certificate['coefficient_factors']
    expected = 2**f['2']*3**f['3']*cr.var('beta')**f['beta']
    need(final[1].terms == expected.terms, 'actual DAG leading coefficient')
    need(sum(final[0]) == packet['exact_degree'] == certificate['exact_degree'], 'actual exact total degree')
    return {'all_live_nodes': len(values), 'exact_center_cut': override is not None,
            'upper_bound_and_attained_coefficient': True}


def coefficient_checks():
    binding = json.loads((ROOT/'coefficients/BINDING.json').read_text())
    ports = {}
    need(list(binding['payloads']) == PORTS, 'complete whole coefficient tuple')
    for name, pin in binding['payloads'].items():
        raw = gzip.decompress((ROOT/'coefficients'/pin['file']).read_bytes())
        need(hashlib.sha256(raw).hexdigest() == pin['raw_sha256'], 'whole payload hash '+name)
        need(len(raw) == pin['raw_bytes'], 'payload byte count '+name)
        ports[name] = int.from_bytes(raw, 'little')
        need(ports[name].bit_length() == pin['bits'], 'payload bit count '+name)
    need(ports['beta'] == 2**1064921-1 and ports['cone_A'] == 2**1113
         and ports['cone_B'] == 2**666104, 'explicit coefficient recipes')
    spec = importlib.util.spec_from_file_location('source34_recipe', ROOT/'coefficients/recipe/source34_builder.py')
    recipe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(recipe)
    rebuilt, recipe_audit = recipe.construct()
    for old, new in [('beta', 'beta'), ('K', 'K0'), ('MC', 'MC'), ('MF_source', 'MF')]:
        need(rebuilt[old] == ports[new], 'full coefficient recipe equality '+new)
    need(ports['cone_A'] % 2 == ports['cone_B'] % 2 == 0, 'even cone coefficients for guard refinement')
    return {'payloads_authenticated': 6, 'recipe_rebuilt': True, 'recipe_audit': recipe_audit}


def main():
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for name, pin in pins['files'].items():
        raw = (ROOT/name).read_bytes()
        need(len(raw) == pin['bytes'] and hashlib.sha256(raw).hexdigest() == pin['sha256'], 'retained source '+name)
    result = {'status': 'PASS', 'source_files_authenticated': len(pins['files']),
              'universal': universal(), 'coefficients': coefficient_checks(), 'equations': []}
    for name in NAMES:
        packet = json.loads((ROOT/(name+'.json')).read_text())
        degree = degree_certificate(packet['centered'])
        result['equations'].append({'name': name, 'topology': topology(packet),
            'all_register_identities': local_checks(packet), 'degree': degree,
            'actual_DAG_leading': actual_leading(packet, degree)})
    # Rebuild is a distinct reproducibility check; identities above do not
    # import the producer or assume its formulas.
    import build
    for centered, name in [(False, NAMES[0]), (True, NAMES[1])]:
        raw = json.dumps(build.build(centered), indent=2)+'\n'
        need(raw == (ROOT/(name+'.json')).read_text(), 'exact artifact regeneration '+name)
    result['exact_artifact_regeneration'] = True
    output = ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'source_files': result['source_files_authenticated'],
                     'equations': [{k: e[k] for k in ['name', 'topology', 'degree']}
                                   for e in result['equations']]}, indent=2))


if __name__ == '__main__':
    main()
