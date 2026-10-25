#!/usr/bin/env python3
"""CODE ONLY / HOLD: independent four-graph audit; never imports the producer."""
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
CASES = [('unsheared_V2', 'doubled_84', 436), ('unsheared_bV', 'doubled_85', 328),
         ('qcube_V2', 'qcube_81', 750), ('qcube_bV', 'qcube_82', 560)]
PORTS = ['beta', 'K0', 'MC', 'MF']
CORE = {'build.py', 'check.py', 'PROOF.md', 'README.md', 'BOUNDARY.md', 'COPIED_INPUTS.json'}
SEALS = {'research/ten-positive-doubled-product-square': 'e9acadc97bd47672184229d9ea59a8f0b5857a3dfd5289f42af17d1af64e967f',
         'research/ten-positive-qcube-doubled-finite': '3e3b5eeb1d5a5c75d58a6ea5dbcf3510ff64ddb2942c8abb47fb4cae39efdd75',
         'research/ten-positive-qcube-doubled': '8051545cea9a38d96c96d3542773aa10fa30c34f3993623d8bb40c02cfa9ab73',
         'research/indexed-tile-enumeration': 'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84',
         'research/ten-positive-uncentered-b-weight': 'e4fe2d2e3d502619cfda003341fd08b49efea408ccdd569d3a551c64dd8f7ac0',
         'research/ten-positive-unshift-t-square': 'cd512697068035f284ebbcbe642dfc2e2c305997e49dbf4e869383f94dd519ac',
         'research/ten-positive-unshift-t-bv': '5a78450ea50bff647c725ac8698dc0d1126edb16167f26ee42bd45ad80876e15'}
VENDOR_SHA = '5d5c645ea19b16e9fac9b4169e21106779af6f5d309e7878009d6d98576d51bc'
SCOPE = ('Positive-zero equivalence uses the sealed ordinary V2 or general bV theorem; '
         'formal T_old=T-alpha is not a positive inverse. Whole indexed/native contracts retained.')


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def load(path):
    return json.loads(path.read_bytes())


def inventory(folder, manifest):
    members = load(manifest)['files']
    actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p != manifest}
    need(actual == set(members), 'Exact whole closed inventory ' + str(folder))
    for name, record in members.items():
        path = folder / name
        raw = path.read_bytes()
        need(not path.is_symlink() and digest(raw) == (record if isinstance(record, str) else record['sha256']), 'Whole closed member ' + name)
        need(isinstance(record, str) or len(raw) == record['bytes'], 'Closed member length ' + name)


def authenticate():
    pins = load(HERE / 'SOURCE_PINS.json')
    need(set(pins['core']) == CORE and pins['required_seals'] == SEALS, 'Complete reviewed core and theorem set')
    for group, folder in [('core', HERE), ('external_whole_files', ROOT)]:
        for name, record in pins[group].items():
            path = folder / name
            raw = path.read_bytes()
            need(not path.is_symlink() and digest(raw) == record['sha256'] and len(raw) == record['bytes'], 'Entire reviewed file ' + name)
    for name, seal in SEALS.items():
        folder = ROOT / name
        manifest = folder / 'MANIFEST.json'
        need(digest(manifest.read_bytes()) == seal, 'Exact accepted ordinary/source seal')
        inventory(folder, manifest)
    copies = load(HERE / 'COPIED_INPUTS.json')['files']
    actual_copies = {p.relative_to(HERE).as_posix() for folder in ['parents', 'vendor', 'provenance', 'coefficients']
                     for p in (HERE / folder).rglob('*') if p.is_file() or p.is_symlink()}
    need(actual_copies == set(copies), 'Complete exact copied-input inventory')
    for name, record in copies.items():
        path = HERE / name
        raw = path.read_bytes()
        need(not path.is_symlink() and raw == (ROOT / record['source']).read_bytes() and
             digest(raw) == record['sha256'] and len(raw) == record['bytes'], 'Whole accepted copy ' + name)
    need({n for n in copies if n.startswith('parents/')} == {'parents/' + stem + '.json' for _, stem, _ in CASES}, 'Four whole parent copies')
    need(digest((HERE / 'vendor/verify.py').read_bytes()) == VENDOR_SHA, 'Selected exact accepted sparse utility')
    if (HERE / 'MANIFEST.json').exists():
        inventory(HERE, HERE / 'MANIFEST.json')
    return pins, copies


def whole_ports(folder):
    binding = load(HERE / 'parents/doubled_84.json')['coefficient_binding']
    for _, stem, _ in CASES:
        need(load(HERE / ('parents/' + stem + '.json'))['coefficient_binding'] == binding, 'Entire tuple shared by all four parents')
    need(binding == load(HERE / 'provenance/indexed-binding.json'), 'Entire directly indexed binding')
    values, records = {}, []
    for name, record in binding['ports'].items():
        rawfile = (folder / 'coefficients' / record['file']).read_bytes()
        need(rawfile == (ROOT / 'research/ten-positive-doubled-product-square/coefficients' / record['file']).read_bytes(), 'Whole accepted compressed coefficient ' + name)
        raw = gzip.decompress(rawfile)
        value = int.from_bytes(raw, 'little')
        need(digest(rawfile) == record['gzip_sha256'] and digest(raw) == record['raw_sha256'] and
             value.bit_length() == record['bits'] and len(raw) == (record['bits'] + 7) // 8, 'Canonical whole raw coefficient ' + name)
        values[name] = value
        records.append({'port': name, 'raw_bytes': len(raw), 'bits': record['bits'], 'raw_sha256': digest(raw)})
    need(set(values) == set(PORTS) and values['beta'] >= 31 and values['beta'] % 2 == 1 and values['K0'] > 0 and
         0 < values['MC'] < values['beta'] < values['MF'] < 2 * values['beta'], 'Complete actual coefficient box')
    return binding, records


def graph(packet, parent, degree):
    need(packet['domain'] == parent['domain'] == 'strictly positive integers' and packet['witnesses'] == parent['witnesses'] and
         packet['fixed_numerals'] == PORTS and packet['output'] == 'N', 'Exact positive signature, four ports and output')
    known = set(packet['witnesses'] + PORTS)
    degrees = {n: int(n in packet['witnesses']) for n in known}
    definitions = {}
    need(type(packet['source']) is list, 'Whole literal row list')
    for row in packet['source']:
        need(type(row) is list and len(row) == 4, 'Actual binary gate row')
        name, op, a, b = row
        need(type(name) is str and name not in known and op in ['+', '-', '*'], 'Unique fresh defined gate')
        need(all(type(x) is int or type(x) is str and x in known for x in [a, b]), 'Topological literal operands')
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
    counts = dict(Counter(r[1] for r in packet['source']))
    need(live == known and len(definitions) == packet['operations'] and counts == packet['operation_breakdown'], 'Every gate/input/port live; actual complete counts')
    need(degrees['N'] == degree == packet['exact_degree'], 'Whole degree upper bound')
    return definitions, counts


def metadata(packet, parent, case, stem, degree, copies):
    expected = deepcopy(parent)
    local = 'parents/' + stem + '.json'
    source = copies[local]['source']
    folder = source.split('/data/')[0] if '/data/' in source else source.rsplit('/', 1)[0]
    theorem = 'research/ten-positive-unshift-t-' + ('square' if case.endswith('V2') else 'bv')
    ancestry = {'path': source, 'sha256': digest((HERE / local).read_bytes()), 'manifest_sha256': SEALS[folder]}
    ordinary = {'path': theorem + '/PROPOSAL.md', 'manifest_sha256': SEALS[theorem]}
    expected.update(name='unshift_T_' + parent['name'], source=packet['source'], operations=len(packet['source']),
                    operation_breakdown=dict(Counter(r[1] for r in packet['source'])), exact_degree=degree,
                    proof='PROOF.md', proof_status=SCOPE, unshift_parent=ancestry, unshift_ordinary=ordinary)
    need(encoded(packet) == encoded(expected), 'All new and inherited typed metadata, including all four whole ports')
    return ancestry, ordinary


def correspondence(packet, parent, declaration, stem):
    rows = packet['source']
    positions = {r[0]: i for i, r in enumerate(rows)}
    need([r for r in parent['source'] if r[0] == 'Tp'] == [['Tp', '+', 'T', 'alpha']] and
         [r for r in parent['source'] if 'Tp' in r[2:]] == [['cT', '*', 'c', 'Tp']], 'Actual entire private alias occurrence set')
    entries, order, inverse = [], [], []
    for i, old in enumerate(parent['source']):
        name = old[0]
        if name == 'Tp':
            need(name not in positions, 'Exactly removed private alias')
            action, j, row = 'deleted', None, None
        else:
            need(name in positions, 'Every surviving parent row')
            j, row = positions[name], rows[positions[name]]
            wanted = ['cT', '*', 'c', 'T'] if name == 'cT' else old
            need(row == wanted, 'Complete unchanged or solely rewired row ' + name)
            action = 'rewritten' if name == 'cT' else 'retained'
            order.append(name)
            inverse.append(i)
        entries.append({'old_index': i, 'old_row': old, 'action': action, 'new_index': j, 'new_row': row})
    need([r[0] for r in rows] == order, 'Entire row order with only private deletion')
    expected = {'parent_local': 'parents/' + stem + '.json', 'rows': entries, 'new_to_old': inverse,
                'formal_parent_substitution': {'T': 'T-alpha'},
                'positive_parent_to_new': {'T_new': 'T_old+alpha', 'other_inputs': 'fixed'},
                'positive_new_to_parent': 'Decode refutation and rebuild canonical witnesses; no positive formal inverse.'}
    need(encoded(declaration) == encoded(expected), 'Whole typed old/new maps and explicitly existential positive inverse')
    return {'old_rows': len(parent['source']), 'new_rows': len(rows), 'removed': ['Tp'], 'rewritten': ['cT']}


def cuts(case):
    qcube, small = case.startswith('qcube'), case.endswith('bV')
    result = [('bJ', 'beta*J'), ('q', 'bJ+1')]
    if qcube:
        result.append(('Y', 'q*q*q*s'))
    result += [('C', 'q-F-alpha'), ('X', 'w*q'), ('k', 'eta+zeta'), ('c', 'k*Y+eta'),
               ('mu', 'q*q+1'), ('Am1', 'mu*Y*(X+1)'), ('Hp', '4*Am1-1'),
               ('V0', 'X*mu*mu*Y*Y'), ('Dtau', '1+V0*(V0+1)*k*k'),
               ('R', '(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'), ('e', 'k-R-1'),
               ('Bt', '(K0+w)*C-F'), ('Delta', 'Am1*(Am1+2)'), ('U', 'i*c*c'),
               ('DpI2', 'Delta*U*U*Dtau'), ('Df', '1+DpI2'), ('Fsqr', '1+4*DpI2*Df'),
               ('Q', '4*Delta*DpI2*Df'), ('cTR', 'c*T-R'), ('V', 'Fsqr*cTR-c')]
    if not qcube:
        result.append(('P1', 'q*q*q*bJ'))
    result += [('center', 'n-' + ('cTR*V' if small else 'V*V') + '*Bt'), ('Kpos', 'X*(3*c-2*X)+2')]
    carrier = ('bJ*mu*mu*(Hp*center+Kpos)-Hp*(mu*mu*Bt+bJ*e)' if qcube else
               'P1*mu*mu*(Hp*center+Kpos)+Hp*(mu*mu*(bJ*Y-q*q*q*Bt)-P1*e)')
    result += [('Znum', carrier), ('Mtot', ('bJ' if qcube else 'P1') + '*mu*mu*Hp'), ('Dg', 'Dtau*Df'),
               ('N', 'Q*(Znum*Znum-Mtot*Mtot*Dg*V*V)+(Mtot*Mtot*Dg-Znum*Znum)')]
    return result


def semantic(packet, definitions, case, kernel):
    available, covered, records = set(packet['witnesses'] + PORTS), set(), []
    for target, text in cuts(case):
        wanted, boundary = kernel.expression(text)
        need(boundary <= available, 'Previously justified independent polynomial boundary ' + target)
        memo = {n: kernel.variable(n) for n in boundary}
        def expand(name):
            if type(name) is int:
                return kernel.constant(name)
            if name in memo:
                return memo[name]
            need(name in definitions, 'No unbound cut leaf ' + str(name))
            op, a, b = definitions[name]
            covered.add(name)
            aa, bb = expand(a), expand(b)
            memo[name] = kernel.multiply(aa, bb) if op == '*' else kernel.add(aa, bb, -1 if op == '-' else 1)
            return memo[name]
        actual = expand(target)
        need(actual == wanted, 'Entire collected free-port identity ' + target)
        records.append({'target': target, 'formula': text, 'terms': len(actual), 'polynomial_sha256': digest(repr(sorted(actual.items())).encode())})
        available.add(target)
    need(covered == set(definitions) and len(records) == 29, 'All actual live gates covered by 29 independent cuts')
    return records


def universal_parent_identity(packet, parent, kernel):
    new = {r[0]: r for r in packet['source']}
    old_substitution = {'T': kernel.expression('T-alpha')[0], 'Tp': kernel.variable('T')}
    def operand(x, old):
        if type(x) is int:
            return kernel.constant(x)
        return old_substitution.get(x, kernel.variable(x)) if old else kernel.variable(x)
    def rhs(row, old):
        _, op, a, b = row
        aa, bb = operand(a, old), operand(b, old)
        return kernel.multiply(aa, bb) if op == '*' else kernel.add(aa, bb, -1 if op == '-' else 1)
    records = []
    for row in parent['source']:
        wanted = kernel.variable('T') if row[0] == 'Tp' else rhs(new[row[0]], False)
        actual = rhs(row, True)
        need(actual == wanted, 'Whole-row formal parent identity ' + row[0])
        records.append({'old_target': row[0], 'terms': len(actual), 'sha256': digest(repr(sorted(actual.items())).encode())})
    need(len(records) == len(parent['source']), 'Induction covers every parent gate through N')
    return {'formal_substitution': 'T_old=T-alpha, all other independent inputs and all four ports fixed',
            'entire_polynomial_identity': 'N_old(T-alpha)=N_new(T)', 'all_old_rows': records,
            'positive_scope': 'This all-integer identity is not a positive inverse; canonical reconstruction is the ordinary theorem.'}


def highest(packet, case, kernel):
    variables = packet['witnesses'] + PORTS
    zero = (0,) * len(variables)
    def C(n):
        return {zero: n} if n else {}
    def V(name):
        exponents = [0] * len(variables)
        exponents[variables.index(name)] = 1
        return {tuple(exponents): 1}
    def add(a, b, sign=1):
        out = dict(a)
        for m, n in b.items():
            out[m] = out.get(m, 0) + sign*n
        return {m: n for m, n in out.items() if n}
    def mul(a, b):
        out = {}
        for m, c in a.items():
            for n, d in b.items():
                k = tuple(x+y for x, y in zip(m, n))
                out[k] = out.get(k, 0) + c*d
        return {m: c for m, c in out.items() if c}
    def power(a, n):
        out = C(1)
        while n:
            if n % 2:
                out = mul(out, a)
            n //= 2
            if n:
                a = mul(a, a)
        return out
    def prod(*polys):
        out = C(1)
        for poly in polys:
            out = mul(out, poly)
        return out
    env = {n: (int(n in packet['witnesses']), V(n)) for n in variables}
    operand = lambda x: (0, C(x)) if type(x) is int else env[x]
    per_gate = []
    for name, op, a, b in packet['source']:
        da, aa = operand(a)
        db, bb = operand(b)
        if op == '*':
            degree, poly = da+db, mul(aa, bb)
        elif da > db:
            degree, poly = da, aa
        elif db > da:
            degree, poly = db, ({m: -c for m, c in bb.items()} if op == '-' else bb)
        else:
            degree, poly = da, add(aa, bb, -1 if op == '-' else 1)
        need(poly and all(sum(m[:10]) == degree for m in poly), 'Full nonvanishing homogeneous component, no cancellation shortcut ' + name)
        env[name] = degree, poly
        per_gate.append({'gate': name, 'degree': degree, 'terms': len(poly)})
    q, k = mul(V('beta'), V('J')), add(V('eta'), V('zeta'))
    r = add(q, V('F'), -1)
    c = add(r, V('alpha'), -1)
    small, qcube = case.endswith('bV'), case.startswith('qcube')
    if qcube:
        expected = prod(C(-(2**10) if small else 2**14), power(V('i'), 14 if small else 20),
                        power(q, 384 if small else 506), power(V('w'), 34 if small else 46),
                        power(V('s'), 80 if small else 108), power(k, 46 if small else 64), power(V('T'), 2 if small else 4))
        if not small:
            expected = mul(expected, power(c, 2))
        witness = '-2^10*beta^384' if small else '2^14*beta^506'
    else:
        expected = prod(C(-(2**10) if small else 2**14), power(q, 156 if small else 200),
                        power(V('w'), 34 if small else 46), power(V('Y'), 78 if small else 104),
                        power(V('i'), 14 if small else 20), power(k, 44 if small else 60), power(r, 2 if small else 4))
        if not small:
            expected = mul(expected, power(c, 2))
        witness = '-2^10*beta^156' if small else '2^14*beta^200'
    degree, actual = env['N']
    need(degree == packet['exact_degree'] and actual == expected, 'Complete multivariate collected global leading form')
    vector = [[n, list(m)] for m, n in sorted(actual.items())]
    return {'degree': degree, 'variables': variables, 'entire_coefficient_vector': vector,
            'full_vector_sha256': digest(encoded(vector)), 'nonzero_selected_coefficient': witness,
            'per_gate_homogeneous_collection': per_gate, 'no_ray_or_assumed_cancellation': True}


def data_inventory(folder):
    need(not (folder / 'data').is_symlink(), 'No generated-directory symlink')
    index = load(folder / 'data/INDEX.json')
    names = {'data/equation_' + case + '.json' for case, _, _ in CASES} | {'data/ROW_MAPS.json', 'data/METRICS.json', 'data/CALIBRATION_BINDING.json'}
    need(set(index) == {'schema', 'producer_sha256', 'source_pins_sha256', 'files'} and index['schema'] == 'unshift_T_four_complete_graphs_v1', 'Entire data index schema')
    need(index['producer_sha256'] == digest((HERE / 'build.py').read_bytes()) and
         index['source_pins_sha256'] == digest((HERE / 'SOURCE_PINS.json').read_bytes()), 'Whole producer/core index binding')
    need(set(index['files']) == names, 'All four complete graphs and three metadata artifacts')
    actual = {p.relative_to(folder).as_posix() for p in (folder / 'data').rglob('*') if p.is_file()}
    need(actual == names | {'data/INDEX.json'}, 'Closed generated file set')
    for name, record in index['files'].items():
        path = folder / name
        raw = path.read_bytes()
        need(set(record) == {'sha256', 'bytes'} and type(record['bytes']) is int and not path.is_symlink() and
             digest(raw) == record['sha256'] and len(raw) == record['bytes'], 'Whole typed actual indexed artifact ' + name)


def verify(packet, parent, declaration, case, stem, degree, copies, kernel):
    definitions, counts = graph(packet, parent, degree)
    ancestry, ordinary = metadata(packet, parent, case, stem, degree, copies)
    rows = correspondence(packet, parent, declaration, stem)
    return {'case': case, 'operations': len(definitions), 'operation_breakdown': counts,
            'whole_row_correspondence': rows, 'free_port_cuts': semantic(packet, definitions, case, kernel),
            'universal_parent_identity': universal_parent_identity(packet, parent, kernel),
            'complete_global_leading_form': highest(packet, case, kernel), 'entire_parent': ancestry, 'ordinary_equivalence': ordinary}


def controls(packets, maps, copies, kernel):
    rejected, positives = [], []
    def reject(label, action):
        try:
            action()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise ValueError('Actual corruption not rejected: ' + label)
    for case, stem, degree in CASES:
        parent, original = load(HERE / ('parents/' + stem + '.json')), packets[case]
        for label, change in [
            ('positive domain', lambda p: p.update(domain='integers')),
            ('signature order', lambda p: p['witnesses'].reverse()),
            ('whole tuple metadata', lambda p: p['coefficient_binding']['ports']['MC'].update(bits=1)),
            ('parent whole hash', lambda p: p['unshift_parent'].update(sha256='0'*64)),
            ('ordinary seal', lambda p: p['unshift_ordinary'].update(manifest_sha256='0'*64)),
            ('stale count', lambda p: p.update(operations=1000)),
            ('stale degree', lambda p: p.update(exact_degree=1)),
            ('forward reference', lambda p: p['source'][0].__setitem__(2, 'N')),
            ('duplicate gate', lambda p: p['source'][1].__setitem__(0, p['source'][0][0])),
            ('missing gate', lambda p: p['source'].pop(1)),
            ('private Tp consumer restored', lambda p: next(r for r in p['source'] if r[0]=='cT').__setitem__(3, 'Tp'))]:
            bad = deepcopy(original)
            change(bad)
            with TemporaryDirectory(prefix='unshift-T-graph-control-') as temporary:
                path = Path(temporary) / 'actual.json'
                path.write_bytes(encoded(bad))
                reject(case+': '+label, lambda: verify(load(path), parent, maps[case], case, stem, degree, copies, kernel))
        for label, target, column, value in [('wrong raw T', 'cT', 3, 'alpha'), ('undoubled V', 'DfcTR', 2, 'Df'),
                                             ('wrong transport weight', 'LBt', 2, 'V'),
                                             ('carrier B sign', 'Znum', 1, '+' if case.startswith('qcube') else '-')]:
            bad = deepcopy(original)
            next(r for r in bad['source'] if r[0] == target)[column] = value
            definitions = {r[0]: tuple(r[1:]) for r in bad['source']}
            reject(case+': semantic '+label, lambda: semantic(bad, definitions, case, kernel))
        bad = deepcopy(original)
        next(r for r in bad['source'] if r[0] == 'Qinside')[2] = 'Dtau'
        reject(case+': complete leading form mutation', lambda: highest(bad, case, kernel))
        for label, change in [('row inverse', lambda m: m['new_to_old'].__setitem__(0, -1)),
                              ('formal positive inverse', lambda m: m['formal_parent_substitution'].update(T='T+alpha')),
                              ('deleted row map', lambda m: next(r for r in m['rows'] if r['action']=='deleted').update(action='retained'))]:
            bad = deepcopy(maps[case])
            change(bad)
            with TemporaryDirectory(prefix='unshift-T-map-control-') as temporary:
                path = Path(temporary) / 'actual.json'
                path.write_bytes(encoded(bad))
                reject(case+': '+label, lambda: correspondence(original, parent, load(path), stem))
        for op in ['+', '*']:
            good = deepcopy(original)
            row = next(r for r in good['source'] if r[1] == op)
            row[2], row[3] = row[3], row[2]
            definitions, _ = graph(good, parent, degree)
            semantic(good, definitions, case, kernel)
            highest(good, case, kernel)
            positives.append(case+': semantic commuted '+op+' (literal exact-row identity is separately enforced)')
    with TemporaryDirectory(prefix='unshift-T-payload-control-') as temporary:
        folder = Path(temporary)
        (folder / 'coefficients').mkdir()
        for path in (HERE / 'coefficients').iterdir():
            (folder / 'coefficients' / path.name).write_bytes(path.read_bytes())
        path = folder / 'coefficients/MC.bin.gz'
        raw = bytearray(gzip.decompress(path.read_bytes()))
        raw[0] ^= 1
        path.write_bytes(gzip.compress(bytes(raw), mtime=0))
        reject('whole actual raw payload', lambda: whole_ports(folder))
    with TemporaryDirectory(prefix='unshift-T-data-control-') as temporary:
        folder = Path(temporary)
        (folder / 'data').mkdir()
        for path in (HERE / 'data').iterdir():
            (folder / 'data' / path.name).write_bytes(path.read_bytes())
        path = folder / 'data/INDEX.json'
        original = load(path)
        for label, change in [('index producer', lambda p: p.update(producer_sha256='0'*64)),
                              ('index file omission', lambda p: p['files'].pop('data/METRICS.json'))]:
            bad = deepcopy(original)
            change(bad)
            path.write_bytes(encoded(bad))
            reject(label, lambda: data_inventory(folder))
        path.write_bytes(encoded(original))
        target = folder / 'data/METRICS.json'
        target.write_bytes(target.read_bytes()+b' ')
        reject('whole actual indexed data bytes', lambda: data_inventory(folder))
    need(len(rejected) == 80 and len(positives) == 8, 'All planned actual graph/map/payload/index controls')
    return {'negative_count': len(rejected), 'negative_labels': rejected, 'positive_count': len(positives), 'positive_labels': positives}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins, copies = authenticate()
    fixed_binding, ports = whole_ports(HERE)
    data_inventory(HERE)
    spec = importlib.util.spec_from_file_location('accepted_sparse_polynomial_utilities', HERE / 'vendor/verify.py')
    need(spec is not None and spec.loader is not None, 'Reviewed import specification')
    kernel = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(kernel)
    maps, packets, records, metrics, calibration = load(HERE / 'data/ROW_MAPS.json'), {}, [], [], {}
    need(set(maps) == {case for case, _, _ in CASES}, 'All four complete maps')
    for case, stem, degree in CASES:
        packet = load(HERE / ('data/equation_' + case + '.json'))
        parent = load(HERE / ('parents/' + stem + '.json'))
        parent_definitions, parent_counts = graph(parent, parent, degree)
        need(packet['coefficient_binding'] == fixed_binding, 'Whole fixed instance in actual graph')
        record = verify(packet, parent, maps[case], case, stem, degree, copies, kernel)
        record['whole_parent_actual_census'] = {'operations': len(parent_definitions), 'operation_breakdown': parent_counts, 'all_gates_inputs_ports_live': True}
        records.append(record)
        packets[case] = packet
        metrics.append({'case': case, 'file': 'data/equation_'+case+'.json', 'positive_inputs': len(packet['witnesses']),
                        'operations': record['operations'], 'operation_breakdown': record['operation_breakdown'],
                        'degree_to_be_independently_collected': degree})
        calibration[case] = {'entire_parent': record['entire_parent'], 'ordinary_equivalence': record['ordinary_equivalence'],
                             'whole_coefficient_binding': fixed_binding,
                             'canonical_requirements': ['R>3q', 'R=3 mod4', 'q^3 divides Y', 'fresh positive witnesses'],
                             'scope': 'Direct whole-parent and ordinary theorem composition; no fresh native/compiler/runtime theorem.'}
    need(encoded(load(HERE / 'data/METRICS.json')) == encoded(metrics) and
         encoded(load(HERE / 'data/CALIBRATION_BINDING.json')) == encoded(calibration), 'Every typed actual census and complete ordinary calibration binding')
    result = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize), 'checker_sha256': digest(Path(__file__).read_bytes()),
              'source_pins_sha256': digest((HERE / 'SOURCE_PINS.json').read_bytes()), 'complete_equations': records,
              'whole_actual_ports': ports, 'whole_raw_payload_bytes': sum(r['raw_bytes'] for r in ports),
              'actual_controls': controls(packets, maps, copies, kernel), 'external_pins': len(pins['external_whole_files']),
              'closed_theorems': SEALS, 'no_producer_import_or_optimizer': True,
              'scope': 'Complete finite algebra/maps/global leading forms; unbounded positive/native equivalence remains the exact sealed ordinary theorem.'}
    raw = encoded(result)
    output = args.output.resolve()
    protected = {(HERE / n).resolve() for n in CORE | {'SOURCE_PINS.json', 'HOLD_INVENTORY.json', 'MANIFEST.json'}}
    directories = [(HERE / n).resolve() for n in ['data', 'parents', 'vendor', 'provenance', 'coefficients']]
    need(not args.output.is_symlink() and output not in protected and not any(p == output or p in output.parents for p in directories) and
         (not args.output.exists() or args.output.read_bytes() == raw), 'Fresh receipt or identical existing receipt only')
    args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
