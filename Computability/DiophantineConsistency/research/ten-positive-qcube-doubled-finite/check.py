#!/usr/bin/env python3
"""Held independent full-row/free-port/degree checker; never imports the producer."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = 'research/ten-positive-doubled-product-square'
SOURCE_SEAL = 'e9acadc97bd47672184229d9ea59a8f0b5857a3dfd5289f42af17d1af64e967f'
PROPOSAL = 'research/ten-positive-qcube-doubled'
PROPOSAL_SEAL = '8051545cea9a38d96c96d3542773aa10fa30c34f3993623d8bb40c02cfa9ab73'
VENDOR_SHA = '5d5c645ea19b16e9fac9b4169e21106779af6f5d309e7878009d6d98576d51bc'
INPUTS = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
VARIABLES = INPUTS + PORTS
CASES = [(84, 81, 750, 'V2'), (85, 82, 560, 'bV')]


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def authenticate():
    pins = load(HERE / 'SOURCE_PINS.json')
    for group, folder in [('core', HERE), ('external_whole_files', ROOT)]:
        for name, record in pins[group].items():
            data = (folder / name).read_bytes()
            need(digest(data) == record['sha256'] and len(data) == record['bytes'],
                 'Whole reviewed dependency ' + name)
    need({d['path']: d['sha256'] for d in pins['closed_dependencies']} == pins['required_seals'],
         'All closed calibration dependencies')
    need(pins['required_seals'].get(SOURCE) == SOURCE_SEAL and
         pins['required_seals'].get(PROPOSAL) == PROPOSAL_SEAL, 'Exact accepted source and ordinary theorem')
    for record in pins['closed_dependencies']:
        folder = ROOT / record['path']
        manifest = folder / 'MANIFEST.json'
        need(digest(manifest.read_bytes()) == record['sha256'], 'Exact ordinary/source seal')
        members = load(manifest)['files']
        actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*')
                  if p.is_file() and p != manifest}
        need(actual == set(members), 'Whole ordinary/source inventory')
        for name, entry in members.items():
            data = (folder / name).read_bytes()
            need(digest(data) == (entry if isinstance(entry, str) else entry['sha256']),
                 'Entire inherited member ' + name)
            need(isinstance(entry, str) or len(data) == entry['bytes'], 'Inherited member length')
    if (HERE / 'MANIFEST.json').exists():
        manifest = HERE / 'MANIFEST.json'
        members = load(manifest)['files']
        actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob('*')
                  if p.is_file() and p != manifest}
        need(actual == set(members), 'Closed final author inventory')
        for name, record in members.items():
            data = (HERE / name).read_bytes()
            need(digest(data) == record['sha256'] and len(data) == record['bytes'], 'Final whole member')
    copied = load(HERE / 'COPIED_INPUTS.json')['files']
    need(set(copied) == {'parents/equation_84.json', 'parents/equation_85.json', 'parents/PROPOSAL.md',
                         'vendor/verify.py', 'coefficients/K.bin.gz', 'coefficients/MC.bin.gz',
                         'coefficients/MF_source.bin.gz', 'coefficients/beta.bin.gz'}, 'Eight exact local copies')
    for name, record in copied.items():
        data = (HERE / name).read_bytes()
        need(data == (ROOT / record['source']).read_bytes() and digest(data) == record['sha256']
             and len(data) == record['bytes'], 'Whole original accepted copy ' + name)
    need(digest((HERE / 'vendor/verify.py').read_bytes()) == VENDOR_SHA, 'Exact selected polynomial kernel')
    return pins


def binding(folder):
    parent = load(HERE / 'parents/equation_84.json')
    need(parent['coefficient_binding'] == load(HERE / 'parents/equation_85.json')['coefficient_binding'],
         'One complete parent tuple')
    result, values = [], {}
    for name, pin in parent['coefficient_binding']['ports'].items():
        rawfile = (folder / 'coefficients' / pin['file']).read_bytes()
        need(rawfile == (ROOT / SOURCE / 'coefficients' / pin['file']).read_bytes(),
             'Whole accepted compressed port ' + name)
        raw = gzip.decompress(rawfile)
        value = int.from_bytes(raw, 'little')
        need(digest(rawfile) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'] and
             value.bit_length() == pin['bits'] and len(raw) == (pin['bits'] + 7) // 8,
             'Entire raw canonical unsigned little-endian port ' + name)
        values[name] = value
        result.append({'port': name, 'bytes': len(raw), 'bits': pin['bits'], 'raw_sha256': digest(raw)})
    need(set(values) == set(PORTS) and values['beta'] >= 31 and values['beta'] % 2 == 1 and
         values['K0'] > 0 and 0 < values['MC'] < values['beta'] < values['MF'] < 2 * values['beta'],
         'Whole actual coefficient instance')
    return parent['coefficient_binding'], result


def source_rows(packet, old, new, degree, weight, fixed_binding):
    parent_bytes = (HERE / f'parents/equation_{old}.json').read_bytes()
    fields = {'name', 'domain', 'witnesses', 'fixed_numerals', 'coefficient_binding', 'source',
              'output', 'operations', 'operation_breakdown', 'exact_degree', 'transport_weight',
              'proof', 'proof_status', 'parent', 'ordinary_proposal'}
    need(set(packet) == fields, 'Entire new metadata schema')
    expected = {'name': 'qcube_doubled_product_square_' + weight,
                'domain': 'strictly positive integers', 'witnesses': INPUTS, 'fixed_numerals': PORTS,
                'coefficient_binding': fixed_binding, 'output': 'N', 'operations': new,
                'operation_breakdown': {'*': 48 if new == 81 else 49, '+': 19, '-': 14},
                'exact_degree': degree, 'transport_weight': weight, 'proof': 'PROOF.md',
                'proof_status': 'Complete ordinary positive maps relative to the whole accepted indexed/native contracts; canonical q^3|Y and R>3q retained. No page or Lean promotion.',
                'parent': {'path': SOURCE + f'/equation_{old}.json', 'sha256': digest(parent_bytes),
                           'manifest_sha256': SOURCE_SEAL},
                'ordinary_proposal': {'path': PROPOSAL + '/PROPOSAL.md', 'manifest_sha256': PROPOSAL_SEAL}}
    for key, value in expected.items():
        need(packet[key] == value, 'Fixed whole metadata ' + key)
    need(type(packet['source']) is list, 'Complete literal binary source')
    known = set(INPUTS + PORTS)
    degrees = {name: 1 if name in INPUTS else 0 for name in known}
    definitions = {}
    for row in packet['source']:
        need(type(row) is list and len(row) == 4, 'One actual binary row')
        name, op, a, b = row
        need(type(name) is str and name not in known and op in ['+', '-', '*'], 'Fresh binary gate')
        need(all(type(x) is int or type(x) is str and x in known for x in [a, b]),
             'Strict topological literal operands')
        da, db = [0 if type(x) is int else degrees[x] for x in [a, b]]
        degrees[name] = da + db if op == '*' else max(da, db)
        definitions[name] = (op, a, b)
        known.add(name)
    live, stack = set(), ['N']
    while stack:
        name = stack.pop()
        if type(name) is int or name in live:
            continue
        live.add(name)
        stack.extend(definitions.get(name, ('',))[1:])
    counts = dict(Counter(row[1] for row in packet['source']))
    need(live == known and len(definitions) == new and counts == expected['operation_breakdown'],
         'All complete actual rows/inputs/ports live and counted')
    need(degrees['N'] == degree, 'Actual global degree upper bound')
    return definitions, counts


def row_correspondence(packet, parent, declaration):
    rows = packet['source']
    positions = {row[0]: i for i, row in enumerate(rows)}
    removed = {'P1', 'qm1Y', 'q3Bt', 'inner'}
    moved = {'q2', 'q3'}
    replacements = {'P1mu2': ['P1mu2', '*', 'bJ', 'mu2'],
                    'mu2inner': ['mu2inner', '*', 'mu2', 'Bt'],
                    'P1e': ['P1e', '*', 'bJ', 'e'], 'brk': ['brk', '+', 'mu2inner', 'P1e'],
                    'Znum': ['Znum', '-', 'Zpart1', 'Zpart2']}
    order = []
    expected_map = []
    for index, original in enumerate(parent['source']):
        name = original[0]
        if name not in removed | moved:
            order.append(name)
            if name == 'q':
                order.extend(['q2', 'q3', 'Y'])
        if name in removed:
            need(name not in positions, 'Only specified obsolete gate absent')
            action, new_index, new_row = 'deleted', None, None
        else:
            need(name in positions, 'Every retained parent coordinate')
            new_index, new_row = positions[name], rows[positions[name]]
            need(new_row == replacements.get(name, original), 'Entire retained or rewritten parent row ' + name)
            action = 'moved' if name in moved else 'rewritten' if name in replacements else 'retained'
        expected_map.append({'old_index': index, 'old_row': original, 'action': action,
                             'new_index': new_index, 'new_row': new_row})
    need([r[0] for r in rows] == order and rows[positions['Y']] == ['Y', '*', 'q3', 's'],
         'Entire new row order and unique added square-free Y gate')
    expected = {'parent': parent['operations'], 'rows': expected_map,
                'added': [{'new_index': positions['Y'], 'row': rows[positions['Y']]}],
                'formal_old_input_substitution': {'Y': 'q^3*s', 'n': 'n-s'},
                'scope': 'Formal polynomial row correspondence; not a positive old-tuple bijection.'}
    need(declaration == expected, 'Every declared old/new row and formal input mapping')
    return {'old_rows': len(parent['source']), 'new_rows': len(rows), 'removed': sorted(removed),
            'moved': sorted(moved), 'rewritten': sorted(replacements), 'added': ['Y']}


def cuts(weight):
    return [('bJ', 'beta*J'), ('q', 'bJ+1'), ('Y', 'q*q*q*s'), ('C', 'q-F-alpha'),
            ('X', 'w*q'), ('k', 'eta+zeta'), ('c', 'k*Y+eta'), ('mu', 'q*q+1'),
            ('Am1', 'mu*Y*(X+1)'), ('Hp', '4*Am1-1'), ('V0', 'X*mu*mu*Y*Y'),
            ('Dtau', '1+V0*(V0+1)*k*k'), ('R', '(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),
            ('e', 'k-R-1'), ('Bt', '(K0+w)*C-F'), ('Delta', 'Am1*(Am1+2)'),
            ('U', 'i*c*c'), ('DpI2', 'Delta*U*U*Dtau'), ('Df', '1+DpI2'),
            ('Fsqr', '1+4*DpI2*Df'), ('Q', '4*Delta*DpI2*Df'), ('cTR', 'c*(T+alpha)-R'),
            ('V', 'Fsqr*cTR-c'), ('center', 'n-' + ('V*V' if weight == 'V2' else 'cTR*V') + '*Bt'),
            ('Kpos', 'X*(3*c-2*X)+2'),
            ('Znum', 'bJ*mu*mu*(Hp*center+Kpos)-Hp*(mu*mu*Bt+bJ*e)'),
            ('Mtot', 'bJ*mu*mu*Hp'), ('Dg', 'Dtau*Df'),
            ('N', 'Q*(Znum*Znum-Mtot*Mtot*Dg*V*V)+(Mtot*Mtot*Dg-Znum*Znum)')]


def semantic(packet, definitions, kernel):
    available, covered, certificate = set(INPUTS + PORTS), set(), []
    for target, text in cuts(packet['transport_weight']):
        expected, boundary = kernel.expression(text)
        need(boundary <= available, 'Previously proved free boundary ' + target)
        memo = {name: kernel.variable(name) for name in boundary}
        def expand(name):
            if type(name) is int:
                return kernel.constant(name)
            if name in memo:
                return memo[name]
            need(name in definitions, 'Bound literal semantic node ' + name)
            op, a, b = definitions[name]
            covered.add(name)
            aa, bb = expand(a), expand(b)
            memo[name] = kernel.multiply(aa, bb) if op == '*' else kernel.add(aa, bb, -1 if op == '-' else 1)
            return memo[name]
        actual = expand(target)
        need(actual == expected, 'Entire free-port polynomial interface ' + target)
        certificate.append({'target': target, 'terms': len(actual),
                            'sha256': digest(repr(sorted(actual.items())).encode())})
        available.add(target)
    need(covered == set(definitions) and len(certificate) == 29, 'All literal gates covered by29 exact cuts')
    return certificate


def clearing(kernel):
    ex = lambda text: kernel.expression(text)[0]
    old = ex('q**3*h*mu**2*(H*(n-s-L*B)+K)+H*(mu**2*(h*q**3*s-q**3*B)-q**3*h*e)')
    new = ex('h*mu**2*(H*(n-L*B)+K)-H*(mu**2*B+h*e)')
    need(old == kernel.multiply(ex('q**3'), new), 'Whole unconditional old/new carrier identity')
    need(ex('q**3*h*mu**2*H') == kernel.multiply(ex('q**3'), ex('h*mu**2*H')),
         'Whole denominator identity')
    need(ex('Q*((q**3*Z)**2-(q**3*M)**2*G*V**2)+((q**3*M)**2*G-(q**3*Z)**2)') ==
         kernel.multiply(ex('q**6'), ex('Q*(Z**2-M**2*G*V**2)+(M**2*G-Z**2)')),
         'Whole degree-two finalizer scaling q^6')
    return {'carrier': 'Zold=q^3*Z', 'denominator': 'Mold=q^3*M', 'polynomial': 'Nold=q^6*N',
            'domain_note': 'Formal oldn=n-s can be nonpositive; direct soundness is the pinned ordinary theorem.'}


ZERO = (0,) * len(VARIABLES)


def C(value):
    return {ZERO: value} if value else {}


def V(name):
    exponents = [0] * len(VARIABLES)
    exponents[VARIABLES.index(name)] = 1
    return {tuple(exponents): 1}


def add(a, b, sign=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + sign * c
    return {m: c for m, c in out.items() if c}


def mul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(x + y for x, y in zip(m, n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}


def power(poly, n):
    out = C(1)
    while n:
        if n % 2:
            out = mul(out, poly)
        n //= 2
        if n:
            poly = mul(poly, poly)
    return out


def prod(*polys):
    out = C(1)
    for poly in polys:
        out = mul(out, poly)
    return out


def highest(packet, number):
    env = {n: (1 if n in INPUTS else 0, V(n)) for n in VARIABLES}
    operand = lambda x: (0, C(x)) if type(x) is int else env[x]
    for name, op, a, b in packet['source']:
        da, aa = operand(a)
        db, bb = operand(b)
        if op == '*':
            degree, poly = da + db, mul(aa, bb)
        elif da > db:
            degree, poly = da, aa
        elif db > da:
            degree, poly = db, ({m: -c for m, c in bb.items()} if op == '-' else bb)
        else:
            degree, poly = da, add(aa, bb, -1 if op == '-' else 1)
        need(poly and all(sum(m[:len(INPUTS)]) == degree for m in poly),
             'Nonvanishing entire homogeneous component at every gate ' + name)
        env[name] = degree, poly
    q0, k0, T0 = mul(V('beta'), V('J')), add(V('eta'), V('zeta')), add(V('T'), V('alpha'))
    small = number == 82
    expected = prod(C(-(2 ** 10) if small else 2 ** 14), power(V('i'), 14 if small else 20),
                    power(q0, 384 if small else 506), power(V('w'), 34 if small else 46),
                    power(V('s'), 80 if small else 108), power(k0, 46 if small else 64),
                    power(T0, 2 if small else 4))
    if not small:
        expected = mul(expected, power(add(add(q0, V('F'), -1), V('alpha'), -1), 2))
    degree, actual = env['N']
    need(degree == (560 if small else 750) and actual == expected, 'Full actual global highest form')
    vector = [[coefficient, list(m)] for m, coefficient in sorted(actual.items())]
    return {'degree': degree, 'terms': len(vector), 'full_vector_sha256': digest(encoded(vector)),
            'variables': VARIABLES, 'nonzero_coefficient': '-2^10*beta^384' if small else '2^14*beta^506',
            'scope': 'Complete symbolic highest form, not a ray or only a zero-set identity; actual beta>0.'}


def controls(kernel, fixed_binding, packets, maps):
    rejected, positives = [], []
    def reject(label, action):
        try:
            action()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise ValueError('Undetected actual artifact mutation ' + label)
    for old, number, degree, weight in CASES:
        original = packets[number]
        def verify(candidate):
            defs, _ = source_rows(candidate, old, number, degree, weight, fixed_binding)
            semantic(candidate, defs, kernel)
        for label, change in [
                ('input domain', lambda p: p.update(domain='unrestricted integers')),
                ('s input', lambda p: p['witnesses'].__setitem__(6, 'Y')),
                ('declared count', lambda p: p.update(operations=number + 1)),
                ('declared degree', lambda p: p.update(exact_degree=degree - 1)),
                ('whole tuple', lambda p: p['coefficient_binding']['ports']['MF'].update(bits=1)),
                ('parent seal', lambda p: p['parent'].update(manifest_sha256='0' * 64)),
                ('ordinary seal', lambda p: p['ordinary_proposal'].update(manifest_sha256='0' * 64)),
                ('Y square instead of cube', lambda p: next(r for r in p['source'] if r[0] == 'Y').__setitem__(2, 'q2')),
                ('old clearing multiplier', lambda p: next(r for r in p['source'] if r[0] == 'P1mu2').__setitem__(2, 'q3')),
                ('old inner sign', lambda p: next(r for r in p['source'] if r[0] == 'brk').__setitem__(1, '-')),
                ('old carrier sign', lambda p: next(r for r in p['source'] if r[0] == 'Znum').__setitem__(1, '+')),
                ('forward reference', lambda p: p['source'][0].__setitem__(2, 'N')),
                ('duplicate coordinate', lambda p: p['source'][1].__setitem__(0, p['source'][0][0])),
                ('wrong finalizer', lambda p: p['source'][-1].__setitem__(1, '-'))]:
            bad = deepcopy(original)
            change(bad)
            with TemporaryDirectory(prefix='qcube-doubled-json-control-') as temporary:
                path = Path(temporary) / 'actual.json'
                path.write_bytes(encoded(bad))
                reject(f'{number}: {label}', lambda: verify(load(path)))
        parent = load(HERE / f'parents/equation_{old}.json')
        for label, change in [
                ('row index', lambda m: m['rows'][0].update(new_index=-1)),
                ('deleted row', lambda m: next(r for r in m['rows'] if r['action'] == 'deleted').update(action='retained')),
                ('positive reverse shear claim', lambda m: m['formal_old_input_substitution'].update(n='n'))]:
            bad = deepcopy(maps[str(number)])
            change(bad)
            with TemporaryDirectory(prefix='qcube-doubled-map-control-') as temporary:
                path = Path(temporary) / 'actual_map.json'
                path.write_bytes(encoded(bad))
                reject(f'{number}: {label}', lambda: row_correspondence(original, parent, load(path)))
        for op in ['+', '*']:
            good = deepcopy(original)
            row = next(r for r in good['source'] if r[1] == op)
            row[2], row[3] = row[3], row[2]
            verify(good)
            positives.append(f'{number}: commuted {op} operands')
    with TemporaryDirectory(prefix='qcube-doubled-payload-control-') as temporary:
        folder = Path(temporary)
        (folder / 'coefficients').mkdir()
        for path in (HERE / 'coefficients').iterdir():
            (folder / 'coefficients' / path.name).write_bytes(path.read_bytes())
        target = folder / 'coefficients/MC.bin.gz'
        raw = bytearray(gzip.decompress(target.read_bytes()))
        raw[0] ^= 1
        target.write_bytes(gzip.compress(bytes(raw), mtime=0))
        reject('entire actual raw coefficient mutation', lambda: binding(folder))
    need(len(rejected) == 35 and len(positives) == 4, 'All planned actual graph/map/payload controls')
    return {'negative_labels': rejected, 'negative_count': len(rejected),
            'positive_labels': positives, 'positive_count': len(positives)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins = authenticate()
    fixed_binding, ports = binding(HERE)
    spec = importlib.util.spec_from_file_location('accepted_sparse_polynomial_kernel', HERE / 'vendor/verify.py')
    need(spec is not None and spec.loader is not None, 'Exact kernel import specification')
    kernel = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(kernel)
    index = load(HERE / 'data/INDEX.json')
    need(index['schema'] == 'qcube_doubled_full_literal_data_v1' and
         index['producer_sha256'] == digest((HERE / 'build.py').read_bytes()), 'Whole deterministic producer binding')
    need(set(index['files']) == {'data/equation_81.json', 'data/equation_82.json',
                                'data/ROW_MAPS.json', 'data/METRICS.json'}, 'Entire generated artifact inventory')
    for name, record in index['files'].items():
        data = (HERE / name).read_bytes()
        need(digest(data) == record['sha256'] and len(data) == record['bytes'], 'Whole indexed data ' + name)
    need({p.name for p in (HERE / 'data').iterdir() if p.is_file()} ==
         {'INDEX.json', 'ROW_MAPS.json', 'METRICS.json', 'equation_81.json', 'equation_82.json'},
         'Closed generated data inventory')
    maps, packets, records, metrics = load(HERE / 'data/ROW_MAPS.json'), {}, [], []
    need(set(maps) == {'81', '82'}, 'Both complete row maps')
    for old, number, degree, weight in CASES:
        packet = load(HERE / f'data/equation_{number}.json')
        parent = load(HERE / f'parents/equation_{old}.json')
        kernel.audit(parent)  # The exact accepted old full graph; no main/file access.
        definitions, counts = source_rows(packet, old, number, degree, weight, fixed_binding)
        correspondence = row_correspondence(packet, parent, maps[str(number)])
        certificate = semantic(packet, definitions, kernel)
        leading = highest(packet, number)
        records.append({'file': f'data/equation_{number}.json', 'operations': len(definitions),
                        'operation_breakdown': counts, 'all_inputs_ports_and_rows_live': True,
                        'complete_row_correspondence': correspondence, 'free_port_cuts': certificate,
                        'entire_highest_form': leading})
        metrics.append({'file': f'data/equation_{number}.json', 'positive_inputs': len(INPUTS),
                        'operations': len(definitions), 'operation_breakdown': counts,
                        'claimed_degree_pending_independent_check': degree,
                        'scope': 'Counts of complete emitted rows, not manual parent-count subtraction.'})
        packets[number] = packet
    need(load(HERE / 'data/METRICS.json') == metrics, 'Every generated metric independently recounted')
    result = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
              'scope': 'Complete actual literal graphs/maps/whole tuple/free-port identities/full global degrees; ordinary positive maps and native calibration remain the pinned unbounded theorem.',
              'equations': records, 'whole_ports': ports, 'whole_raw_payload_bytes': sum(r['bytes'] for r in ports),
              'universal_identity': clearing(kernel), 'actual_artifact_controls': controls(kernel, fixed_binding, packets, maps),
              'whole_external_pins': len(pins['external_whole_files']), 'closed_dependencies': pins['closed_dependencies'],
              'no_producer_import_or_optimizer': True, 'canonical_or_lean_changed': False}
    raw = encoded(result)
    args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
