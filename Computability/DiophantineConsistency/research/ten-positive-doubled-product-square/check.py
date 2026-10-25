#!/usr/bin/env python3
"""Held whole-instance audit; exact incoming kernel plus independent leading forms."""
import argparse
from collections import Counter
from contextlib import redirect_stdout
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import io
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUT_NAMES = ['J', 'F', 'alpha', 'i', 'T', 'w', 'Y', 'n', 'eta', 'zeta']
PORT_NAMES = ['beta', 'K0', 'MC', 'MF']
VARIABLES = INPUT_NAMES + PORT_NAMES
VENDOR_SHA = '5d5c645ea19b16e9fac9b4169e21106779af6f5d309e7878009d6d98576d51bc'
PARENT_SHA = '954731033595b2816d3b852737ec1c05627cebf133b4621543b1c34488901670'
PARENT = 'candidates/one-page-uncentered89'
ARCHIVE = 'docs/incoming/ConZFC_Staged_Certificates_2026-10-24.zip'
ARCHIVE_SHA = 'feca1bfc1d2f1ee9d8af7040e3bb61802d1218cc0760653e878bb7c22cbd5063'
SOURCE_COMMIT = 'fd3e384e92ed4813a5536f877c5cd835ca4c75d2'
SEALS = {
    "research/indexed-tile-enumeration": "e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84",
    "research/ten-positive-saturated-pell": "14961a7122489a6b9f4833892c6f4a67ec4b267ae2cc50f9a7b06c4b6587cd33",
    "research/ten-positive-uncentered-b-weight": "e4fe2d2e3d502619cfda003341fd08b49efea408ccdd569d3a551c64dd8f7ac0",
    "candidates/one-page-uncentered89": "48d5b06bac49cd29669b877b60355b62b3fe213d43cde904f934138663e1e4e6",
    "research/intake-fd3e384e92": "c80f0a1012d06750cccc8783c967eda41c6fe818f57f6a79566f653c5b34de80"
}
EXTRAS = [
    "reviews/staged-certificates-compact-ordinary-peer.md",
    "reviews/staged-certificates-compact-verifier-static-peer.md",
    "con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md",
    "research/ten-positive-zero-offset/PROOF.md",
    "candidates/ten-positive-zero-offset/PROOF.md"
]
CORE_NAMES = ['check.py', 'PROOF.md', 'README.md', 'INPUTS.json', 'VERIFICATION_SCOPE.md']
LOCAL_FILES = {
    'verify.py', 'equation_84.json', 'equation_85.json', 'parent-equation.json',
    'coefficients/K.bin.gz', 'coefficients/MC.bin.gz',
    'coefficients/MF_source.bin.gz', 'coefficients/beta.bin.gz',
    'provenance/SOURCE_LEDGER.json', 'provenance/indexed_constant_specification.tex',
    'provenance/indexed_native_proof.md', 'provenance/parent_printed_equation.tex',
    'provenance/prior_product11_proof.md', 'provenance/saturated_parent_proof.md',
    'provenance/uncentered_parent_proof.md', 'incoming/PROOF.md',
}
PROOF_STATUS = ('New ordinary Pell-doubling/product-square arithmetic equivalence; '
                'consistency interpretation uses the explicitly retained whole indexed '
                'native/source calibration; no new Lean or object-ZFC proof object.')
PACKET_FIELDS = {'name', 'domain', 'witnesses', 'fixed_numerals', 'coefficient_binding',
                 'source', 'output', 'operations', 'operation_breakdown', 'exact_degree',
                 'transport_weight', 'proof', 'proof_status', 'parent_commit',
                 'parent_path', 'parent_sha256'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def authenticate():
    pins = load(HERE / 'SOURCE_PINS.json')
    need(set(pins['core']) == set(CORE_NAMES), 'Entire reviewed five-file core')
    need({r['path']: r['sha256'] for r in pins['closed_dependencies']} == SEALS,
         'All five exact closed ordinary/native/arrival dependencies')
    expected_external = set(EXTRAS)
    for rel in SEALS:
        expected_external.update(p.relative_to(ROOT).as_posix()
                                 for p in (ROOT / rel).rglob('*') if p.is_file())
    need(set(pins['external_whole_files']) == expected_external,
         'Entire independent external closure inventory')
    for name, record in pins['core'].items():
        data = (HERE / name).read_bytes()
        need(len(data) == record['bytes'] and digest(data) == record['sha256'],
             'Reviewed whole core ' + name)
    for name, record in pins['external_whole_files'].items():
        data = (ROOT / name).read_bytes()
        need(len(data) == record['bytes'] and digest(data) == record['sha256'],
             'Whole external dependency ' + name)
    for record in pins['closed_dependencies']:
        folder = ROOT / record['path']
        manifest = folder / 'MANIFEST.json'
        need(digest(manifest.read_bytes()) == record['sha256'], 'Closed dependency seal')
        files = load(manifest)['files']
        actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*')
                  if p.is_file() and p != manifest}
        need(set(files) == actual, 'Closed dependency inventory ' + record['path'])
        for name, member in files.items():
            data = (folder / name).read_bytes()
            expected = member if isinstance(member, str) else member['sha256']
            need(digest(data) == expected, 'Sealed whole dependency member')
            need(isinstance(member, str) or len(data) == member['bytes'], 'Sealed byte length')
    if (HERE / 'MANIFEST.json').exists():
        manifest = HERE / 'MANIFEST.json'
        files = load(manifest)['files']
        actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob('*')
                  if p.is_file() and p != manifest}
        need(set(files) == actual, 'Whole final author inventory')
        for name, record in files.items():
            data = (HERE / name).read_bytes()
            need(digest(data) == record['sha256'] and len(data) == record['bytes'],
                 'Whole final author member ' + name)
    return pins


def exact_copies(folder):
    source = load(HERE / 'INPUTS.json')
    inventory = load(ROOT / 'research/intake-fd3e384e92/INVENTORY.json')
    need(source['source_commit'] == inventory['source_commit'] == SOURCE_COMMIT,
         'Exact original arrival commit')
    archive = next(a for a in inventory['archives'] if a['path'] == ARCHIVE)
    need(source['archive'] == ARCHIVE and source['archive_sha256'] ==
         archive['archive_sha256'] == ARCHIVE_SHA and
         source['archive_git_blob'] == archive['git_blob'], 'Exact original ZIP binding')
    need(set(source['copies']) == LOCAL_FILES, 'Entire selected sixteen-file closure')
    members = {m['name']: m for m in archive['members']}
    total = 0
    for name, record in source['copies'].items():
        expected_member = 'ConZFC_Staged_Certificates_2026-10-24/compact/' + (
            'PROOF.md' if name == 'incoming/PROOF.md' else name)
        need(record['member'] == expected_member and record['member'] in members,
             'Exact original archive member path')
        original = members[record['member']]
        need(record['sha256'] == original['sha256'] and record['bytes'] == original['bytes'],
             'Independent sealed arrival member binding')
        data = (folder / name).read_bytes()
        need(digest(data) == record['sha256'] and len(data) == record['bytes'],
             'Exact whole original input copy ' + name)
        total += len(data)
    need(digest((folder / 'verify.py').read_bytes()) == VENDOR_SHA, 'Unchanged reviewed kernel')
    return {'files': len(LOCAL_FILES), 'bytes': total, 'archive_sha256': ARCHIVE_SHA}


def calibration(folder):
    parent_bytes = (folder / 'parent-equation.json').read_bytes()
    need(digest(parent_bytes) == PARENT_SHA and parent_bytes ==
         (ROOT / PARENT / 'polynomial.json').read_bytes(), 'Whole accepted indexed89 parent')
    parent = json.loads(parent_bytes)
    ledger = load(folder / 'provenance/SOURCE_LEDGER.json')
    need(ledger['commit'] == 'f4d8db99e060339f3306a04d507c35bc1d0d68c5',
         'Historical source-ledger commit')
    for name, record in ledger['files'].items():
        if 'repository_path' in record:
            data = (folder / 'provenance' / name).read_bytes()
            need(digest(data) == record['sha256'] and data ==
                 (ROOT.parent.parent / record['repository_path']).read_bytes(),
                 'Entire native/proof/specification provenance ' + name)
        else:
            need(name == 'prior_product11_proof.md' and 'Comparison and attribution only'
                 in record['role'], 'Nonlogical attribution boundary')
    binding = parent['coefficient_binding']
    need(set(binding['ports']) == set(PORT_NAMES), 'Whole four-port parent instance')
    values = {}
    records = []
    for name, record in binding['ports'].items():
        data = (folder / 'coefficients' / record['file']).read_bytes()
        expected = (ROOT / PARENT / 'coefficients' / record['file']).read_bytes()
        need(data == expected, 'Entire accepted compressed coefficient ' + name)
        raw = gzip.decompress(data)
        expected_raw = gzip.decompress(expected)
        value = int.from_bytes(raw, 'little')
        need(raw == expected_raw and digest(raw) == record['raw_sha256'] and
             digest(data) == record['gzip_sha256'], 'Entire raw coefficient ' + name)
        need(value.bit_length() == record['bits'] and len(raw) == (record['bits'] + 7) // 8,
             'Canonical unsigned little-endian coefficient ' + name)
        values[name] = value
        records.append({'port': name, 'raw_bytes': len(raw), 'bits': record['bits'],
                        'raw_sha256': digest(raw), 'gzip_sha256': digest(data)})
    need(values['beta'] >= 31 and values['beta'] % 2 == 1 and values['K0'] > 0 and
         0 < values['MC'] < values['beta'] < values['MF'] < 2 * values['beta'],
         'Whole authentic coefficient box')
    return binding, values, records


def semantic(packet, number, vendor, binding):
    small = number == 85
    need(set(packet) == PACKET_FIELDS, 'All candidate metadata fields')
    expected = dict(name='pell_doubling_product_square_' + ('bV' if small else 'V2'),
                    domain='strictly positive integers', witnesses=INPUT_NAMES,
                    fixed_numerals=PORT_NAMES, output='N', operations=number,
                    operation_breakdown={'*': 51 if small else 50, '+': 19, '-': 15},
                    exact_degree=328 if small else 436, transport_weight='bV' if small else 'V2',
                    proof='PROOF.md', proof_status=PROOF_STATUS,
                    parent_commit='f4d8db99e060339f3306a04d507c35bc1d0d68c5',
                    parent_path='Computability/DiophantineConsistency/' + PARENT + '/polynomial.json',
                    parent_sha256=PARENT_SHA, coefficient_binding=binding)
    for key, value in expected.items():
        need(packet[key] == value, 'Independently fixed candidate field ' + key)
    need(type(packet['source']) is list, 'Actual binary row list')
    for row in packet['source']:
        need(type(row) is list and len(row) == 4 and type(row[0]) is str and
             type(row[1]) is str and all(type(x) in (str, int) for x in row[2:]),
             'Strict literal binary row/operand types')
    return vendor.audit(packet)


# A separate sparse polynomial representation uses fixed exponent vectors.
# Ports have input weight zero, remain symbolic, and are never mixed tuples.
ZERO_MONOMIAL = (0,) * len(VARIABLES)


def constant(value):
    return {ZERO_MONOMIAL: value} if value else {}


def variable(name):
    monomial = [0] * len(VARIABLES)
    monomial[VARIABLES.index(name)] = 1
    return {tuple(monomial): 1}


def plus(left, right, sign=1):
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, 0) + sign * coefficient
    return {m: c for m, c in result.items() if c}


def times(left, right):
    result = {}
    for m, a in left.items():
        for n, b in right.items():
            monomial = tuple(x + y for x, y in zip(m, n))
            result[monomial] = result.get(monomial, 0) + a * b
    return {m: c for m, c in result.items() if c}


def power(poly, exponent):
    result = constant(1)
    while exponent:
        if exponent % 2:
            result = times(result, poly)
        exponent //= 2
        if exponent:
            poly = times(poly, poly)
    return result


def product(*polys):
    result = constant(1)
    for poly in polys:
        result = times(result, poly)
    return result


def leading_form(packet, number):
    env = {name: (1 if name in INPUT_NAMES else 0, variable(name)) for name in VARIABLES}
    def operand(value):
        return (0, constant(value)) if type(value) is int else env[value]
    for name, op, a, b in packet['source']:
        da, pa = operand(a)
        db, pb = operand(b)
        if op == '*':
            degree, polynomial = da + db, times(pa, pb)
        elif da > db:
            degree, polynomial = da, pa
        elif db > da:
            degree, polynomial = db, ({m: -c for m, c in pb.items()} if op == '-' else pb)
        else:
            degree, polynomial = da, plus(pa, pb, -1 if op == '-' else 1)
        need(polynomial, 'Leading component cancellation needs a new certificate at ' + name)
        need(all(sum(m[:len(INPUT_NAMES)]) == degree for m in polynomial),
             'Homogeneous degree at every actual gate')
        env[name] = degree, polynomial
    q0 = times(variable('beta'), variable('J'))
    k0 = plus(variable('eta'), variable('zeta'))
    common = [power(q0, 156 if number == 85 else 200),
              power(variable('w'), 34 if number == 85 else 46),
              power(variable('Y'), 78 if number == 85 else 104),
              power(variable('i'), 14 if number == 85 else 20),
              power(k0, 44 if number == 85 else 60)]
    qf = plus(q0, variable('F'), -1)
    if number == 85:
        expected = product(constant(-(2 ** 10)), *common, power(qf, 2))
    else:
        expected = product(constant(2 ** 14), *common, power(qf, 4),
                           power(plus(qf, variable('alpha'), -1), 2))
    degree, actual = env['N']
    need(degree == (328 if number == 85 else 436) and actual == expected,
         'Full actual highest homogeneous form at all free coefficient ports')
    vector = [[c, list(m)] for m, c in sorted(actual.items())]
    return {'degree': degree, 'terms': len(vector), 'variables': VARIABLES,
            'full_leading_vector_sha256': digest(json.dumps(vector, separators=(',', ':')).encode()),
            'nonzero_witness': '-2^10*beta^156' if number == 85 else '2^14*beta^200',
            'scope': 'Entire symbolic highest form; beta is the authenticated positive fixed port.'}


def artifact_controls(vendor, binding):
    negative = []
    positive = []
    originals = {n: load(HERE / f'equation_{n}.json') for n in (84, 85)}
    def reject(label, action):
        try:
            action()
        except (ValueError, KeyError, TypeError, IndexError, OSError):
            negative.append(label)
        else:
            raise ValueError('Undetected actual artifact mutation: ' + label)
    # Every modified JSON is written and re-read. Outer input digests are
    # intentionally bypassed here, so the deeper checks must reject it.
    for number, original in originals.items():
        mutations = [
            ('domain', lambda p: p.update(domain='nonnegative integers')),
            ('input order', lambda p: p['witnesses'].reverse()),
            ('missing port', lambda p: p['fixed_numerals'].pop()),
            ('operation count', lambda p: p.update(operations=number + 1)),
            ('degree claim', lambda p: p.update(exact_degree=p['exact_degree'] - 1)),
            ('parent binding', lambda p: p.update(parent_sha256='0' * 64)),
            ('proof binding', lambda p: p.update(proof='incoming/PROOF.md')),
            ('tuple binding', lambda p: p['coefficient_binding']['ports']['MF'].update(bits=1)),
            ('duplicate gate', lambda p: p['source'][1].__setitem__(0, p['source'][0][0])),
            ('forward operand', lambda p: p['source'][0].__setitem__(2, 'N')),
            ('Boolean operand', lambda p: p['source'][0].__setitem__(3, True)),
            ('binary operator', lambda p: p['source'][0].__setitem__(1, '**')),
            ('doubling factor', lambda p: next(r for r in p['source'] if r[0] == 'fouraF0').__setitem__(2, 2)),
            ('undoubled kernel', lambda p: next(r for r in p['source'] if r[0] == 'DfcTR').__setitem__(2, 'Df')),
            ('final sign', lambda p: p['source'][-1].__setitem__(1, '-')),
        ]
        for label, mutate in mutations:
            bad = deepcopy(original)
            mutate(bad)
            with TemporaryDirectory(prefix='doubled-product-json-control-') as temporary:
                path = Path(temporary) / 'actual.json'
                path.write_text(json.dumps(bad))
                reject(f'{number}: {label}', lambda: semantic(load(path), number, vendor, binding))
        for op in ('+', '*'):
            good = deepcopy(original)
            row = next(r for r in good['source'] if r[1] == op)
            row[2], row[3] = row[3], row[2]
            semantic(good, number, vendor, binding)
            positive.append(f'{number}: commuted {op} operands')
    for label, name in [('raw coefficient', 'coefficients/MC.bin.gz'),
                        ('parent whole object', 'parent-equation.json'),
                        ('native proof', 'provenance/indexed_native_proof.md'),
                        ('coherent constant recipe', 'provenance/indexed_constant_specification.tex'),
                        ('source ledger', 'provenance/SOURCE_LEDGER.json')]:
        with TemporaryDirectory(prefix='doubled-product-file-control-') as temporary:
            folder = Path(temporary)
            for rel in LOCAL_FILES:
                target = folder / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((HERE / rel).read_bytes())
            target = folder / name
            if name.endswith('.gz'):
                raw = bytearray(gzip.decompress(target.read_bytes()))
                raw[0] ^= 1
                target.write_bytes(gzip.compress(bytes(raw), mtime=0))
            elif name.endswith('SOURCE_LEDGER.json'):
                altered = load(target)
                altered['commit'] = '0' * 40
                target.write_text(json.dumps(altered))
            else:
                target.write_bytes(target.read_bytes() + b'\n')
            reject(label, lambda: calibration(folder))
            reject(label + ' exact-copy ledger', lambda: exact_copies(folder))
    return {'negative_count': len(negative), 'negative_labels': negative,
            'positive_count': len(positive), 'positive_labels': positive}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--copy-check', action='store_true',
                        help='Exact original-input copy check only; not a circuit rebuild')
    args = parser.parse_args()
    pins = authenticate()
    copies = exact_copies(HERE)
    binding, values, payloads = calibration(HERE)
    result = {'schema': 'doubled_product_square_whole_packet_v1', 'status': 'PASS',
              'optimized_python': not __debug__, 'copy_check_only': args.copy_check,
              'copies': copies, 'entire_fixed_tuple': payloads,
              'whole_external_pins': len(pins['external_whole_files']),
              'ordinary_boundary': 'Authored PROOF with actual canonical R>3q; inherited whole indexed/native contracts.',
              'architecture_rebuild_claimed': False, 'canonical_page_changed': False}
    if not args.copy_check:
        spec = importlib.util.spec_from_file_location('reviewed_staged_compact_kernel', HERE / 'verify.py')
        need(spec is not None and spec.loader is not None, 'Reviewed kernel import specification')
        vendor = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(vendor)
        previous_argv = sys.argv
        capture = io.StringIO()
        try:
            sys.argv = [str(HERE / 'verify.py')]
            with redirect_stdout(capture):
                vendor.main()
        finally:
            sys.argv = previous_argv
        kernel = json.loads(capture.getvalue())
        need(kernel['status'] == 'passed' and kernel['gcd_stress_controls'] == 5880,
             'Complete unchanged finite kernel replay')
        equations = []
        for number in (84, 85):
            packet = load(HERE / f'equation_{number}.json')
            degrees, interfaces = semantic(packet, number, vendor, binding)
            need(len(interfaces) == 29 and degrees['N'] == packet['exact_degree'],
                 'All free-port semantic interfaces and exact degree upper bound')
            equations.append({'operations': number, 'operation_breakdown': dict(Counter(r[1] for r in packet['source'])),
                              'all_live_gates': len(packet['source']), 'semantic_interfaces': interfaces,
                              'full_leading_form': leading_form(packet, number),
                              'actual_tuple_exact_ray': vendor.polynomial_ray(packet, values)})
        result.update(equations=equations, kernel_result=kernel,
                      kernel_stdout_sha256=digest(capture.getvalue().encode()),
                      artifact_controls=artifact_controls(vendor, binding))
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
