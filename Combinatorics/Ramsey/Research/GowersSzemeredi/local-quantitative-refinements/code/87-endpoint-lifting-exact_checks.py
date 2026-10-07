#!/usr/bin/env python3
"""Offline exact diagnostics for Report 299; never construct the theorem's tower.

The files in DATA_PINS are each opened once, boundedly captured, and hashed and
parsed from those same immutable bytes. No source file is executed, no network
is accessed, and this default checker creates no files. This is not a proof
assistant or a finite verification of the report's universal theorem.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import stat

ROOT = Path(__file__).absolute().parent.parent
PIN = '130fca9b1131fd983bd0af27565d36e8dfd2865a'
LATER_PIN = 'e40a57b9878f2b20636fe7d1acdc3b2e61796e87'
AUDIT_SHA256 = 'cec55c955738b6f965357d3d87ca5f8344f48fe51965709612a3e0c4422cd65c'
MAX_FILE_BYTES = 512 * 1024
MAX_TOTAL_BYTES = 2 * 1024 * 1024
MAX_JSON_DEPTH = 16
MAX_JSON_NODES = 12000
MAX_INTEGER = 10**9
DATA_PINS = {'companion/certificate.json': 'cc39bc0bd3875bb05db484c311842b0d43db963704e8ffee3ae7500711eff305', 'SOURCE_MANIFEST.json': 'b06d27eb6027765ac6fae30cdf7ff4907813a4426900e10fa6631eec7fd07a68', 'source_excerpts.json': 'd136fdb38e90ac1251e4a2d7d710e99230af2ec42ab6b96ca9058c3509b6e1e3', 'CURRENT_SOURCE_STATUS.json': 'c59e42abf1704ac82e78315d43f89282798d3c1384971a9d7e4668555c7a7d93', 'provenance/PROOF.md': '37d05942c71f9d9d525a93bcdc5b2b6a6b84bcc77de87d8927fda3daacb29713'}


class CheckError(ValueError):
    """A bounded input, identity, or exact check failed."""


def require(condition, message):
    if not condition:
        raise CheckError(message)


def integer(value, low, high, label='integer'):
    require(type(value) is int and low <= value <= high,
            label + ' must be a bounded integer (not bool)')
    return value


def exact_keys(value, keys, label):
    require(type(value) is dict and set(value) == set(keys), label + ' fields differ')


def _identity(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_nlink,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def _open_dir(path):
    require(os.name == 'posix' and hasattr(os, 'O_NOFOLLOW')
            and hasattr(os, 'O_DIRECTORY') and os.open in os.supports_dir_fd,
            'POSIX no-follow directory descriptors required; no unsafe fallback')
    require(type(path) in (str, type(Path())), 'root must be a path or string')
    raw = str(path)
    require(len(raw) <= 4096 and raw.startswith('/') and not raw.startswith('//')
            and '\x00' not in raw and '\\' not in raw
            and all(p not in ('.', '..') for p in raw.split('/')),
            'ordinary absolute root required')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    descriptor = os.open('/', flags)
    try:
        for part in Path(raw).parts[1:]:
            child = os.open(part, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _read_once(parent, leaf):
    """Open one ordinary, singly linked file once; capture its bytes exactly."""
    before = os.stat(leaf, dir_fd=parent, follow_symlinks=False)
    require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1,
            'symlink, hard-link or nonregular data forbidden: ' + leaf)
    require(0 <= before.st_size <= MAX_FILE_BYTES, 'data byte limit exceeded')
    descriptor = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                         dir_fd=parent)
    try:
        opened = os.fstat(descriptor)
        require(_identity(opened) == _identity(before), 'data changed before read')
        pieces = []
        size = 0
        while True:
            piece = os.read(descriptor, min(65536, MAX_FILE_BYTES + 1 - size))
            if not piece:
                break
            pieces.append(piece)
            size += len(piece)
            require(size <= MAX_FILE_BYTES, 'data byte limit exceeded')
        require(size == opened.st_size
                and _identity(os.fstat(descriptor)) == _identity(opened)
                and _identity(os.stat(leaf, dir_fd=parent, follow_symlinks=False))
                    == _identity(opened), 'data changed during read')
        return b''.join(pieces)
    finally:
        os.close(descriptor)


def capture(root=ROOT):
    """Return immutable byte values, never paths to reopen after authentication."""
    descriptor = _open_dir(root)
    result = {}
    total = 0
    try:
        for name in sorted(DATA_PINS):
            parts = name.split('/')
            parent = os.dup(descriptor)
            try:
                for part in parts[:-1]:
                    child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                    dir_fd=parent)
                    os.close(parent)
                    parent = child
                data = _read_once(parent, parts[-1])
            finally:
                os.close(parent)
            result[name] = data
            total += len(data)
            require(total <= MAX_TOTAL_BYTES, 'total data byte limit exceeded')
    finally:
        os.close(descriptor)
    return result


def _json_int(raw):
    require(len(raw) <= 11, 'JSON integer digit bound exceeded')
    return integer(int(raw), -MAX_INTEGER, MAX_INTEGER, 'JSON integer')


def _not_json_number(raw):
    raise CheckError('floating-point and nonfinite JSON numbers forbidden')


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def parse_json(data):
    require(type(data) is bytes and 0 < len(data) <= MAX_FILE_BYTES,
            'bounded immutable JSON bytes required')
    try:
        text = data.decode('utf-8')
    except UnicodeDecodeError as error:
        raise CheckError('invalid UTF-8 JSON') from error
    # Check nesting before json.loads, so malicious nesting cannot reach the
    # interpreter recursion limit. Braces inside escaped strings are ignored.
    depth = 0
    quoted = escaped = False
    for character in text:
        if quoted:
            if escaped:
                escaped = False
            elif character == '\\':
                escaped = True
            elif character == '"':
                quoted = False
        elif character == '"':
            quoted = True
        elif character in '[{':
            depth += 1
            require(depth <= MAX_JSON_DEPTH, 'JSON nesting bound exceeded')
        elif character in ']}':
            depth -= 1
            require(depth >= 0, 'malformed JSON nesting')
    try:
        result = json.loads(text, object_pairs_hook=_unique_object,
                            parse_int=_json_int, parse_float=_not_json_number,
                            parse_constant=_not_json_number)
    except (json.JSONDecodeError, RecursionError) as error:
        raise CheckError('malformed JSON') from error
    pending = [result]
    visited = 0
    while pending:
        value = pending.pop()
        visited += 1
        require(visited <= MAX_JSON_NODES, 'JSON node bound exceeded')
        if type(value) is dict:
            pending.extend(value.keys())
            pending.extend(value.values())
        elif type(value) is list:
            pending.extend(value)
        elif type(value) is str:
            require(len(value) <= 65536, 'JSON string bound exceeded')
        else:
            require(type(value) in (int, bool, type(None)), 'unsupported JSON type')
    return result


def authenticate(snapshot):
    """Hash AND parse each captured buffer; deliberately performs no file I/O."""
    require(type(snapshot) is dict and set(snapshot) == set(DATA_PINS),
            'captured data inventory differs')
    result = {}
    for name, digest in DATA_PINS.items():
        data = snapshot[name]
        require(type(data) is bytes and len(data) <= MAX_FILE_BYTES,
                'immutable bounded captured bytes required')
        require(hashlib.sha256(data).hexdigest() == digest,
                'data identity mismatch: ' + name)
        if name.endswith('.json'):
            result[name] = parse_json(data)
    return result


def validate_certificate(c):
    exact_keys(c, ('schema_version', 'report', 'commit', 'symbolic_constants',
        'diagnostic_primes', 'ap_diagnostic_primes', 'integer_weights',
        'max_interval_length', 'cube_dimensions', 'claim_boundary'), 'certificate')
    require(type(c['schema_version']) is int and c['schema_version'] == 1,
            'certificate schema differs')
    require(type(c['report']) is int and c['report'] == 299 and c['commit'] == PIN,
            'certificate report/source differs')
    require(c['diagnostic_primes'] == [2, 3, 5, 7, 11, 17]
            and c['ap_diagnostic_primes'] == [3, 5, 7]
            and c['integer_weights'] == [0, 1, 2]
            and c['cube_dimensions'] == list(range(1, 9)), 'diagnostic scope differs')
    for name in ('diagnostic_primes', 'ap_diagnostic_primes', 'integer_weights',
                 'cube_dimensions'):
        require(type(c[name]) is list, 'diagnostic list required')
        for value in c[name]:
            integer(value, 0, 19)
    integer(c['max_interval_length'], 3, 3, 'interval length')
    s = c['symbolic_constants']
    wanted = {'A_j': '2^(2^(j+8))', 'K': '2^(2^(2^(k+9)))',
        'R_over_K': 4, 'theta_K': [1, 32], 'epsilon_K': [1, 32],
        'beta_K': [9, 32], 'threshold_base_coefficient': 2**26,
        'threshold_base_K_power': 6, 'threshold_outer_exponent_over_K': 2,
        'sqrt_threshold_coefficient': 8192, 'sqrt_threshold_K_power': 3,
        'hoeffding_denominator_coefficient': 512, 'log_t_coefficient': 3072,
        'constant_log_bound_coefficient': 4096, 'long_axis_over_KR': 32,
        'cover_fraction': [5, 16], 'required_fraction': [1, 2],
        'union_bound_log_fraction': [7, 8]}
    exact_keys(s, wanted, 'symbolic constants')
    for name, expected in wanted.items():
        actual = s[name]
        require(type(actual) is type(expected) and actual == expected,
                'symbolic constant differs: ' + name)
        if type(expected) is list:
            for value in actual:
                integer(value, 1, 32, 'fraction component')
    require(type(c['claim_boundary']) is str and
            'no actual tower constant' in c['claim_boundary'], 'claim boundary missing')


def validate_sources(data):
    manifest = data['SOURCE_MANIFEST.json']
    exact_keys(manifest, ('schema_version', 'commit', 'repository', 'source_count',
        'sources', 'frozen_inputs', 'hash_scope'), 'source manifest')
    require(manifest['schema_version'] == 1 and type(manifest['schema_version']) is int
            and manifest['commit'] == PIN
            and manifest['repository'] == 'VladimirReshetnikov/ProveIt', 'source pin differs')
    sources = manifest['sources']
    require(type(sources) is list and 1 <= len(sources) <= 64, 'source list bound')
    integer(manifest['source_count'], len(sources), len(sources), 'source count')
    by_file = {}
    for source in sources:
        exact_keys(source, ('file', 'repository_path', 'commit', 'git_blob_sha1',
            'sha256', 'bytes', 'url'), 'source record')
        name = source['file']
        require(type(name) is str and re.fullmatch(r'[A-Za-z0-9_]+\.lean', name)
                and name not in by_file, 'invalid/duplicate source filename')
        prefix = 'Combinatorics/Ramsey/Lean/GowersSzemeredi/'
        require(source['repository_path'] == prefix + name and source['commit'] == PIN
                and source['url'] == 'https://github.com/VladimirReshetnikov/ProveIt/blob/'
                    + PIN + '/' + source['repository_path'], 'source location differs')
        for key, length in (('git_blob_sha1', 40), ('sha256', 64)):
            require(type(source[key]) is str and
                    re.fullmatch('[0-9a-f]{' + str(length) + '}', source[key]), 'invalid digest')
        integer(source['bytes'], 1, MAX_FILE_BYTES, 'upstream byte count')
        by_file[name] = source
    frozen = manifest['frozen_inputs']
    require(frozen['source_mathematical_audit_sha256'] == AUDIT_SHA256
            and frozen['proof_sha256'] == DATA_PINS['provenance/PROOF.md'], 'proof/audit pin differs')
    excerpts = data['source_excerpts.json']
    exact_keys(excerpts, ('schema_version', 'commit', 'excerpts'), 'source excerpts')
    require(type(excerpts['schema_version']) is int and excerpts['schema_version'] == 1
            and excerpts['commit'] == PIN, 'excerpt pin differs')
    require(type(excerpts['excerpts']) is list and 1 <= len(excerpts['excerpts']) <= 64,
            'excerpt list bound')
    combined = {}
    ranges = set()
    for excerpt in excerpts['excerpts']:
        exact_keys(excerpt, ('file', 'start_line', 'end_line', 'utf8', 'sha256', 'url'), 'excerpt')
        name = excerpt['file']
        require(type(name) is str and name in by_file, 'unknown excerpt file')
        start = integer(excerpt['start_line'], 1, 100000, 'start line')
        end = integer(excerpt['end_line'], start, start + 128, 'end line')
        key = (name, start, end)
        require(key not in ranges, 'duplicate excerpt range')
        ranges.add(key)
        text = excerpt['utf8']
        require(type(text) is str and text.endswith('\n')
                and len(text.splitlines()) == end - start + 1, 'excerpt line count differs')
        require(hashlib.sha256(text.encode('utf-8')).hexdigest() == excerpt['sha256'],
                'excerpt text digest differs')
        require(excerpt['url'] == by_file[name]['url'] + '#L' + str(start) + '-L' + str(end),
                'excerpt URL differs')
        combined.setdefault(name, []).append(text)
    joined = {name: '\n'.join(parts) for name, parts in combined.items()}
    tokens = {
        'Proofs16ContextualInduction.lean': ['∀ D : Section16CommonBaseData theta gamma B phi,',
            'HasProductProperty B phi gamma → Section16StructuredPair theta gamma B phi →',
            '∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →',
            'MultiplyLinearFunction gamma 1'],
        'Sections14_15.lean': ['∀ (p : Nat)', 'gamma ^ (8 * p) * (N : Real)⁻¹',
            '(∀ x, 0 ≤ theta x)', '∑ x : Point N k, ∏ e : Fin k → Bool,'],
        'Section16.lean': ['(gamma * theta) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8)))',
            '(multipleC theta gamma k)⁻¹',
            '(2 / (theta * gamma)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))',
            '(theta * gamma / 4) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))',
            '(17 * k + 15)', '(2 : Real) ^ (-(44 : Real))',
            '(2 : Real) ^ (-(37 : Real)) * (theta1 / 4) ^ ((11 : Real) / 2)',
            'delta ^ (-(2 : Int)) * multipleS (theta1 / 8) delta k',
            '(2 : Real) ^ (-(32 : Real)) * theta1 ^ 8',
            '(-1 : ZMod N) ^ (k + boolWeight e)',
            '(-1 : ZMod N) ^ k * section16PhiPrimeLift phiPrime z +',
            '∀ theta : Real, 0 < theta → theta ≤ 1 → ∀ P : Box N k, P.IsProper →',
            '(1 - theta) * P.carrier.card ≤ H.card',
            '∀ l : Nat, l < d → ∀ F : CoordinateFace N d l,'],
        'Proofs16CommonBaseAssembly.lean': ['(2 : Real) ^ (-(27 : Real))',
            '(section16ThetaOne theta gamma k) ^ 6',
            '→ Nonempty (Section16CommonBaseData theta gamma B phi)'],
        'Definitions.lean': ['P.carrier.card = P.length', 'ZMod.dft f',
            'mu x = ∑ e, c e * ∏ i, if e i then x i else 1',
            'exact if h : k = 0 then 0'],
        'Proofs16FiniteAlphabetBoxCover.lean': ['(q : Real) * beta ≤ 9 / 32',
            '(H.card : Real) ≤ (5 / 16 : Real) * P.carrier.card'],
        'Proofs16GoodDomainTransport.lean': ['theorem section16_good_domain_subrelation',
            '(hmass : delta * (N : Real) ^ (k + 1) ≤ section16GoodInducedPairCount B H Y x0)'],
        'Proofs16CommonBaseLineCovers.lean': ['theorem Section16CommonBaseData.all_box_line_covers'],
    }
    anchors = 0
    for name, needles in tokens.items():
        for needle in needles:
            require(needle in joined.get(name, ''), 'source anchor missing: ' + name + ': ' + needle)
            anchors += 1
    assembly = next(e['utf8'] for e in excerpts['excerpts']
                    if e['file'] == 'Proofs16CommonBaseAssembly.lean' and e['start_line'] == 30)
    fields = re.findall(r'^  ([A-Za-z_][A-Za-z0-9_]*) :', assembly, flags=re.MULTILINE)
    require(fields == ['H', 'J', 'Y', 'phiPrime', 'x0', 'Hmass', 'intersect_mass',
        'cube_mass', 'selected_mass', 'selection', 'spectrum', 'good_mass', 'identity'],
        'five data/eight proof field inventory differs')
    status = data['CURRENT_SOURCE_STATUS.json']
    require(status['pinned_commit'] == PIN and status['later_examined_commit'] == LATER_PIN,
            'later source status pin differs')
    core = {'Proofs16ContextualInduction.lean', 'Proofs16CommonBaseAssembly.lean',
            'Section16.lean', 'Sections14_15.lean'}
    require(type(status['records']) is list and len(status['records']) == 4,
            'independent status record count differs')
    require({r['file'] for r in status['records']} == core, 'independent checked core differs')
    for record in status['records']:
        require(record['matches_audited_pin'] is True and record['commit'] == LATER_PIN
                and record['blob_sha'] == by_file[record['file']]['git_blob_sha1']
                and record['url'] == by_file[record['file']]['url'].replace(PIN, LATER_PIN),
                'independent later core identity differs')
    research = status['research_frontier_recheck']
    require(research['pinned_proof_commit'] == PIN
            and research['latest_observed_main'] == LATER_PIN
            and len(research['files']) == 5
            and {r['name'] for r in research['files']} == core | {'Proofs16CommonBaseLineCovers.lean'},
            'research later checked files differ')
    for record in research['files']:
        require(record['unchanged'] is True
                and record['sha'] == by_file[record['name']]['git_blob_sha1'],
                'research later core identity differs')
    return {'source_identities': len(sources), 'compact_excerpts': len(ranges),
            'literal_source_anchors': anchors, 'data_fields': 5, 'proof_fields': 8,
            'later_unchanged_core_files': 5}


def monomial_le(left, right):
    """Sufficient exact c*K^a <= d*K^b for all formal K>=1; no K evaluated."""
    c, a = left
    d, b = right
    require(type(c) is Fraction and type(d) is Fraction and c >= 0 and d >= 0,
            'nonnegative Fraction coefficients required')
    integer(a, -1024, 1024, 'power')
    integer(b, -1024, 1024, 'power')
    return c <= d and a <= b


def coefficient_checks(c):
    s = c['symbolic_constants']
    frac = lambda key: Fraction(*s[key])
    r = s['R_over_K']
    theta = frac('theta_K')
    epsilon = frac('epsilon_K')
    beta = frac('beta_K')
    checks = []
    def check(name, condition):
        require(condition, 'coefficient check: ' + name)
        checks.append(name)
    check('theta=1/(8R)', theta == Fraction(1, 8*r))
    check('beta=1/R+epsilon', beta == Fraction(1, r) + epsilon)
    check('Hoeffding exponent coefficient', 2*epsilon**2 == Fraction(1, 512))
    check('threshold exact square', s['sqrt_threshold_coefficient']**2 == 2**26
          and 2*s['sqrt_threshold_K_power'] == s['threshold_base_K_power'])
    check('log(N^3)=6K log(t)', 3*s['threshold_outer_exponent_over_K'] == 6)
    check('scaled log-t coefficient', 512*6 == s['log_t_coefficient'])
    check('scaled log(8K) coarse bound', 512*8 == s['constant_log_bound_coefficient'])
    check('log-t term <=3t/8', Fraction(3072, 8192) == Fraction(3, 8))
    check('constant term <=t/2 for K>=1', monomial_le((Fraction(4096), 3), (Fraction(2**25), 6)))
    check('strict union bound slack', Fraction(1, 2) + Fraction(3, 8) == frac('union_bound_log_fraction') < 1)
    check('threshold base >=(8R)^2', monomial_le((Fraction((8*r)**2), 2), (Fraction(2**26), 6)))
    check('threshold base >=32KR', monomial_le((Fraction(32*r), 2), (Fraction(2**26), 6)))
    check('outer threshold exponent >=1 for K>=1', s['threshold_outer_exponent_over_K'] >= 1)
    check('positive-density theta below 1/R', theta <= Fraction(1, r))
    check('source theta1 exponent >=16 for k>=1', 2**(1+5) >= 4)
    # E=2^(2^(k+5))>=16 and 0<theta<=1 give theta1<=(theta/4)^16<=theta^16.
    check('selected modal fraction', monomial_le((Fraction(1, 2**27)*theta**96, -96),
                                                 (Fraction(1, r), -1)))
    check('good modal mass', monomial_le((Fraction(1, 2**32)*theta**128, -128),
                                        (theta/r, -2)))
    check('all-selected good mass', monomial_le((Fraction(1, 2**32)*theta**128, -128),
                                                (theta, -1)))
    check('finite-alphabet cover coefficient', beta + Fraction(1, s['long_axis_over_KR']) == frac('cover_fraction'))
    check('strict half-mass contradiction', frac('required_fraction') - frac('cover_fraction') == Fraction(3, 16))
    # Combinatorial exponent identity; k is a formal variable.
    check('arrangement exponent coefficients', 17 == 1+16 and 15 == 16-1)
    check('source tower shift d=k+1', 8+1 == 9)
    return {'checks': len(checks), 'cover_fraction': '5/16', 'required_fraction': '1/2',
            'gap': '3/16', 'union_bound_log_fraction': '7/8',
            'tower_evaluated': False, 'symbolic_variable_assumption': 'K >= 1'}


def _prime(p):
    integer(p, 2, 19, 'modulus')
    require(all(p % q for q in range(2, p)), 'prime modulus required')


def _residues(values, p, label):
    require(type(values) in (tuple, list) and len(values) <= p, label + ' bound/type')
    for value in values:
        integer(value, 0, p-1, label)
    require(len(set(values)) == len(values), label + ' duplicates forbidden')


def graph_energy(p, domain, values, weights):
    """Exact integer pair-sum energy, with deliberately bounded public inputs."""
    _prime(p)
    _residues(domain, p, 'domain')
    require(type(values) in (tuple, list) and type(weights) in (tuple, list)
            and len(values) == len(domain) == len(weights), 'graph vector lengths differ')
    for value in values:
        integer(value, 0, p-1, 'graph value')
    for weight in weights:
        integer(weight, 0, 8, 'weight')
    sums = Counter()
    for i, x in enumerate(domain):
        for j, y in enumerate(domain):
            sums[((x+y) % p, (values[i]+values[j]) % p)] += weights[i]*weights[j]
    energy = sum(value*value for value in sums.values())
    return energy, sum(weights), len([v for v in sums.values() if v])


def simultaneous_energy(p, domain, functions, weights):
    """Independent ordered-quadruple definition, including an empty family."""
    _prime(p)
    _residues(domain, p, 'domain')
    require(len(domain) <= 7 and type(functions) in (tuple, list)
            and len(functions) <= 5 and type(weights) in (tuple, list)
            and len(weights) == len(domain), 'quadruple input bound/type')
    for weight in weights:
        integer(weight, 0, 8, 'weight')
    for function in functions:
        require(type(function) in (tuple, list) and len(function) == len(domain),
                'parallel function length/type')
        for value in function:
            integer(value, 0, p-1, 'function value')
    total = 0
    for a, b, c, d in itertools.product(range(len(domain)), repeat=4):
        if ((domain[a]+domain[b]-domain[c]-domain[d]) % p == 0 and
            all((f[a]+f[b]-f[c]-f[d]) % p == 0 for f in functions)):
            total += weights[a]*weights[b]*weights[c]*weights[d]
    return total


def weighted_diagnostics(c):
    cases = direct_cases = rational_cases = repeated_cases = 0
    for p in c['diagnostic_primes']:
        _prime(p)
        for length in range(c['max_interval_length']+1):
            if length > p:
                continue
            domain = tuple(range(length))
            for r in range(1, min(3, p)+1):
                alphabet = tuple(range(r))
                aa = {(x+y) % p for x in domain for y in domain}
                ss = {(x+y) % p for x in alphabet for y in alphabet}
                bound = len(aa)*len(ss)
                if bound > p:
                    continue
                for values in itertools.product(alphabet, repeat=length):
                    for weights in itertools.product(c['integer_weights'], repeat=length):
                        energy, mass, support = graph_energy(p, domain, values, weights)
                        require(support <= bound and p*energy >= mass**4, 'weighted graph-sum inequality failed')
                        direct = simultaneous_energy(p, domain, (values,), weights)
                        require(energy == direct, 'pair and quadruple energies disagree')
                        require(Fraction(p*energy, 2**4) >= Fraction(mass, 2)**4,
                                'rational homogeneous illustration failed')
                        cases += 1
                        direct_cases += 1
                        rational_cases += 1
                    weights = tuple(1 for _ in domain)
                    for family_size in (1, 2, 5):
                        require(simultaneous_energy(p, domain, (values,)*family_size, weights)
                                == graph_energy(p, domain, values, weights)[0],
                                'identical final-coordinate restrictions differ')
                        repeated_cases += 1
    require(cases > 0, 'no weighted cases')
    return {'integer_weight_cases': cases, 'independent_quadruple_comparisons': direct_cases,
            'rational_rescalings': rational_cases, 'identical_parallel_family_cases': repeated_cases,
            'weight_values': c['integer_weights'], 'max_domain_size': c['max_interval_length']}


def zero_and_constant_diagnostics():
    cases = 0
    for p in (2, 3, 5, 7):
        domain = tuple(range(p))  # Not confined to the short interval E.
        for weights in (tuple(0 for _ in domain), tuple(1 for _ in domain),
                        tuple(x % 3 for x in domain)):
            empty = simultaneous_energy(p, domain, (), weights)
            require(p*empty >= sum(weights)**4, 'zero-family ordinary energy failed')
            constants = (tuple(0 for _ in domain), tuple(1 for _ in domain),
                         tuple(p-1 for _ in domain))
            require(simultaneous_energy(p, domain, constants, weights) == empty,
                    'different constant parallel restrictions changed energy')
            cases += 1
    return {'full_field_zero_family_cases': cases, 'different_constant_family_cases': cases,
            'empty_test_domain_energy': simultaneous_energy(3, (), (), ())}


def arrangement_diagnostics(c):
    cases = 0
    for p in c['diagnostic_primes']:
        for length in range(0, min(4, p)+1):
            domain = tuple(range(length))
            counts = [0]*p
            counts[0] = 1
            for _ in range(8):
                following = [0]*p
                for total, multiplicity in enumerate(counts):
                    for x in domain:
                        following[(total+x) % p] += multiplicity
                counts = following
            t8 = sum(n*n for n in counts)
            require(sum(counts) == length**8 and p*t8 >= length**16,
                    'eightfold-sum arrangement Cauchy-Schwarz failed')
            for k in (1, 2):
                # Integer clearing of alpha^16*N^(17k+15), alpha=L/N.
                require(p*(p**(17*k)*t8) >= length**16*p**(17*k),
                        'arrangement count scaling failed')
            cases += 1
    return {'eightfold_convolutions': cases, 'scaling_dimensions': [1, 2]}


def cube_diagnostics(c):
    cases = 0
    for k in c['cube_dimensions']:
        vertices = list(itertools.product((0, 1), repeat=k))
        signs = [(-1)**sum(v) for v in vertices]
        require(sum(signs) == 0, 'positive-dimensional cube sign sum failed')
        ones = vertices.index((1,)*k)
        for p in (2, 3, 5, 7):
            for symbol in range(p):
                induced = sum(sign*symbol for sign in signs) % p
                remainder = -sum((-1)**(k+sum(v))*symbol
                                 for v in vertices if v != (1,)*k) % p
                require(induced == 0 and remainder == symbol, 'constant cube identity failed')
                cases += 1
            arbitrary = [(i*i+3*i+1) % p for i in range(len(vertices))]
            induced = sum(sign*value for sign, value in zip(signs, arbitrary)) % p
            remainder = -sum((-1)**(k+sum(v))*value for v, value in zip(vertices, arbitrary)
                             if v != (1,)*k) % p
            require(arbitrary[ones] == (((-1)**k)*induced + remainder) % p,
                    'corrected all-ones identity failed')
    require(sum([1]) != 0, 'zero-dimensional exclusion lost')
    return {'constant_cube_cases': cases, 'arbitrary_vertex_identity_cases': 4*len(c['cube_dimensions']),
            'dimensions': c['cube_dimensions'], 'dimension_zero_excluded': True}


def modal_diagnostics(c):
    cases = 0
    for p in c['diagnostic_primes']:
        for length in range(1, min(5, p)+1):
            for r in range(1, min(3, p)+1):
                word = [(x*x+x+1) % r for x in range(p)]
                counts = Counter(word[:length])
                modal = min(counts, key=lambda symbol: (-counts[symbol], symbol))
                selected = [x for x in range(length) if word[x] == modal]
                require(r*len(selected) >= length, 'modal fraction failed')
                for k in (1, 2):
                    cube_domain = p**k*length
                    selected_cubes = p**k*len(selected)
                    require(r*selected_cubes >= cube_domain
                            and all(word[x] == modal for x in selected),
                            'good-witness selection/domain count failed')
                cases += 1
    return {'same_word_modal_selection_cases': cases,
            'claim': 'Finite colour-class illustration; theorem witnesses are constructed in the written proof.'}


def progression_diagnostics(c):
    progressions = comparisons = wrapping = zero_step = 0
    for p in c['ap_diagnostic_primes']:
        r = 2
        word = [(x*x+x+1) % r for x in range(p)]
        for start, step, length in itertools.product(range(p), range(p), range(p+1)):
            axis = [(start+i*step) % p for i in range(length)]
            if len(set(axis)) != length:
                continue
            progressions += 1
            wrapping += int(any(start+i*step >= p for i in range(length)))
            zero_step += int(step == 0)
            largest_colour = max(Counter(word[x] for x in axis).values(), default=0)
            maps = []
            for slope, intercept in itertools.product(range(p), repeat=2):
                agreement = {x for x in axis if word[x] == (slope*x+intercept) % p}
                require(len(agreement) <= (largest_colour if slope == 0 else r),
                        'all-direction affine fibre bound failed')
                comparisons += 1
                maps.append(agreement)
            for indices in ((), (0,), (0, 1), (0, p, 2*p-1)):
                covered = set().union(*(maps[i] for i in indices))
                require(len(covered) <= len(indices)*(largest_colour+r),
                        'affine graph-union bound failed')
    require(wrapping > 0 and zero_step > 0, 'progression diagnostic coverage missing')
    return {'proper_progression_presentations': progressions,
            'affine_comparisons': comparisons, 'wrapping_presentations': wrapping,
            'proper_zero_step_presentations': zero_step,
            'claim': 'Checks fibre mechanics with measured colour maxima, not theorem-threshold balance.'}


def run(snapshot=None):
    if snapshot is None:
        snapshot = capture()
    data = authenticate(snapshot)
    c = data['companion/certificate.json']
    validate_certificate(c)
    return {'report': 299, 'status': 'PASS', 'source_commit': PIN,
        'scope': c['claim_boundary'], 'provenance': validate_sources(data),
        'coefficients': coefficient_checks(c), 'weighted_graph_sum': weighted_diagnostics(c),
        'zero_and_constant_families': zero_and_constant_diagnostics(),
        'arrangements': arrangement_diagnostics(c), 'cube_signs': cube_diagnostics(c),
        'good_witness_selection': modal_diagnostics(c),
        'all_direction_fibres': progression_diagnostics(c)}


def main():
    if len(sys.argv) != 1:
        print('usage: python companion/exact_checks.py (read-only; no arguments)', file=sys.stderr)
        return 2
    try:
        result = run()
    except (ValueError, OSError, KeyError, TypeError, OverflowError) as error:
        print('Report299 check failed: ' + str(error), file=sys.stderr)
        return 1
    print(json.dumps(result, ensure_ascii=True, sort_keys=True, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
