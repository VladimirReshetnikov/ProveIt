#!/usr/bin/env python3
"""Bounded offline coefficient/exponent checks, not a real-variable proof engine."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from fractions import Fraction
import hashlib
import json
from math import factorial
import os
from pathlib import Path
import re
import stat

ROOT = Path(__file__).absolute().parents[1]
COMMIT = 'af74fb522c24a6331886b11db76942642a6a0e42'
PROOF_SHA256 = '967e1b57b5823d5eff3282e48420ec64a35bd3562ca5bdfa19a21081dcb2358c'
MAX_BYTES = 256 * 1024
MAX_INT = 1 << 120
DATA_PINS = {'SOURCE_MANIFEST.json': '77ddabf558987f2790da78d3f282dc591cadf34526bdd22003a177e17b62c236', 'source_excerpts.json': 'e9c01991ad38d7847daa4a285a7880943199bc6811ab55559a28116c1d3ad29c', 'companion/certificate.json': 'f91ac1c45fa3d20e861405f5e50b20a110321f6a22ba61867c3afe279b58296e', 'provenance/PROOF.md': '967e1b57b5823d5eff3282e48420ec64a35bd3562ca5bdfa19a21081dcb2358c'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def integer(value, name='integer', bound=MAX_INT):
    if type(value) is not int or abs(value) > bound:
        raise ValueError(name + ' must be a bounded exact integer')
    return value


def rational(value, name='rational'):
    if type(value) is int:
        value = Fraction(integer(value, name))
    if type(value) is not Fraction:
        raise ValueError(name + ' must be an exact integer or Fraction')
    integer(value.numerator, name); integer(value.denominator, name)
    return value


def pair(value):
    if type(value) is not tuple or len(value) != 2:
        raise ValueError('monomial must be an exponent-pair tuple')
    return tuple(rational(v, 'exponent') for v in value)


def multiply(left, right):
    a, b = pair(left), pair(right)
    return pair((a[0] + b[0], a[1] + b[1]))


def power(value, exponent):
    a = pair(value)
    exponent = rational(exponent, 'monomial power')
    if abs(exponent) > (1 << 76):
        raise ValueError('monomial power outside bounded range')
    return pair((a[0] * exponent, a[1] * exponent))


def integral_pair(value):
    a = pair(value)
    if any(v.denominator != 1 for v in a):
        raise ValueError('integral exponent pair required')
    return [integer(v.numerator) for v in a]


def totalized_divide(numerator, denominator):
    numerator, denominator = rational(numerator), rational(denominator)
    return Fraction(0) if denominator == 0 else rational(numerator / denominator)


def pp_log_from_ratio_log(log_ratio, exponent):
    """Exact PP logarithm when its ratio logarithm is already supplied exactly."""
    log_ratio, exponent = rational(log_ratio), rational(exponent)
    if exponent < 0:
        raise ValueError('nonnegative exponent required')
    return totalized_divide(max(Fraction(0), log_ratio), exponent)


def ceil_nonnegative(value):
    value = rational(value)
    if value < 0:
        raise ValueError('nonnegative ceiling argument required')
    return (value.numerator + value.denominator - 1) // value.denominator


def monomials(d=1 << 42):
    integer(d, 'local density degree')
    if not 1 <= d <= (1 << 76):
        raise ValueError('local density degree outside diagnostic range')
    # Pair [u,v] always denotes 2^u times the indicated base to power v.
    eta = (-4, 32)  # gamma^32 / 16
    theta = multiply((-37, 0), power(eta, Fraction(11, 2)))
    theta_one = multiply((-1882, 0), power(theta, 10477))
    q_bound = multiply((1882, 0), power(theta, -10479))
    spectrum = multiply((74, 0), power(eta, -10))
    alpha = (1, -1)  # alpha = 2/x
    half_alpha = (0, -1)
    a = multiply(multiply((-71, 0), power(alpha, 2)), power(half_alpha, d))
    mu = multiply(multiply((-59, 0), power(alpha, 2)), power(half_alpha, d))
    half_a = multiply(a, (-1, 0))
    b = multiply(multiply((-20, 0), power(a, 2)), power(half_a, 12359))
    t = multiply((-30, 0), power(half_a, 24718))
    w = multiply(mu, b)
    beta = multiply(w, (-1, 0))
    geometry = dict(eta=eta, theta=theta, theta_one=theta_one, q_bound=q_bound,
                    Q=(1 << 20, -(1 << 21)), K=(114, -320),
                    spectrum_bound=spectrum, f=(-100, 448),
                    g=multiply((-14, 0), power((-135, 704), 2)), W=(135, -704))
    fejer = dict(alpha=alpha, a=a, mu=mu, b=b, t=t, w=w, beta=beta)
    return {group: {name: integral_pair(value) for name, value in entries.items()}
            for group, entries in [('geometry_gamma', geometry), ('fejer_x', fejer)]}


def formula_ledger():
    """Transcribed symbolic expressions; strings are never parsed or evaluated."""
    return {
        'conventions': {
            'PP': 'PP(C,D,e)=max{1,max{1,C/D}^(1/e)}; real division is totalized',
            'q_zero': 'u_0=theta_one^2/(16*0)=0; PP(C,D,0)=1',
            'finite_range': 'q in {0,...,floor(Q_bound)}; natural supremum is a finite maximum',
            'positive_range': '0<delta<=1/2; alpha=(delta^5/64000)^16; x=2/alpha>=2',
            'geometric_range': '0<gamma<=1; y=2/gamma>=2; B=y^(2^32)',
            'log': 'log denotes log base 2; ln denotes natural logarithm',
            'natural_subtraction': 'q-1 in the simultaneous threshold is natural subtraction',
        },
        'geometry': {
            'c': '2^(-228*K-1)*gamma^(576*K)',
            'd0': 'theta_one/(64*pi)', 'd': 'min{1,d0/2}',
            'k': 'ceil(K)', 'z': '2^(-155*k)*(gamma^32/16)^(18*k)/k',
            'e': '2^(-13*Q)', 'u_q': 'theta_one^2/(16*q)',
            'v_q': '2^(-12*q)',
            'R_q': 'max{(2*W_2)^(2048^(q-1))+1,PP(8,1,v_q),PP(160+2*gamma^32,gamma^32,v_q)}',
            'I_q': 'PP(R_q+2,d0,u_q)',
            'density_recurrence': 'max{3,max_(0<=q<=floor(Q_bound)) ceil(I_q)}',
            'V': 'max{PP(1,c,e),PP(4,d,e),PP(1,z*d,e)}',
            'integer_budget_q': 'max{V,PP(4,d0,u_q)}',
            'density_integer': 'max_(0<=q<=floor(Q_bound)) ceil(integer_budget_q)',
            'J': 'max{PP(8,1,f),PP(W,1,f),PP(8,(1/4)^g,f*g)}',
            'square_scale': 'PP(J,c,e)',
            'square_power': 'max{PP(4,c^f,e*f),PP(2,(c^f/4)^(g/2),e*f*g/4)}',
            'G': 'max{1,density_recurrence,density_integer,square_scale,square_power}',
            'square_power_log_first': '(2/f+log(c^(-1)))/e',
            'square_power_log_second': '(4/(f*g)+2*log(c^(-1))+4/f)/e',
        },
        'common_fourier': {
            'D': '4207554485', 'gamma': 'x^(-D)',
            'h': '14409429', 'j': '97*h+336',
            'purification_parameters': 'delta0=x^(-h); rho=x^(-j); eta=2^(-44)',
            'M': 'ceil(2^78*x^j)',
            'F_graph': 'max{2*M,ceil(2^175*M^63*x^(j+15*h))}',
            'F': 'max{F_graph,G(x^(-D))}',
        },
        'fejer': {
            'd': '2^42', 'P': '(3!)^2*2^16=2359296',
            'e_f': '2^(-x^(2^53))', 'sigma': 'e_f*t/(2*P)',
            'P_j': '(j!)^2*2^((j+1)^2)', 'W_j': '2^(2^(40*j^3+1))',
            'L_j': 'L_j(eta)=max{W_j,(4*pi/eta)^P_j,4^P_j}+4',
            'Bdry': 'Bdry(epsilon)=L_1(4*pi*epsilon)', 'B0': 'Bdry(1/16)',
            'K_count': 'max{1,2*B0*8^(1-t)}', 'D_count': 'K_count*12^t',
            'C': 'L_3(w)*D_count^(1/P)',
            'E': 'exp((4+6*L_2(1))*(2/a)^25378984)',
            'O': 'max{F,PP(4,1,e_f)}',
            'U': 'max{256,O,PP(12*max{2,max{4,E}},1,e_f)}',
            'T_local': 'max{U,PP(C,1,sigma)}',
            'S': 'max{5,T_local,32/beta,12801/delta^5}',
            'c_iter': 'beta/(8*Bdry(beta/64))', 'n': 'ceil(8/beta)',
            'A': '1+ln(max{1,S})+abs(ln(c_iter))',
            'Q_iter': '2*max{1,16/sigma}', 'H_f': 'exp(A*Q_iter^n)',
        },
        'analytic_envelopes': {
            'geometric': 'log(G(gamma))<=2^(16*(2/gamma)^(2^32))',
            'common': 'log(F(alpha))<=2^(x^(2^65))',
            'iteration': 'n*log(Q_iter)<=x^(2^58)',
            'boundary': 'log(c_iter^(-1))<=x^65',
            'start': 'log(S)<=2^(x^(2^65))',
            'final': 'log(log(H_f))<=x^(2^67)',
            'density': 'x<delta^(-337); 337*2^67<2^76',
            'strict_chain': 'H_f<2^(2^(delta^(-2^76)))<2^(2^(delta^(-2^16384)))',
            'scope': 'These real-variable inequalities are proved in provenance/PROOF.md; they are not certified by this script.',
        },
    }


def integer_checks():
    """Exact small-integer identities and sufficient inequalities, no tower values."""
    checks = {}
    def check(name, left, relation, right):
        integer(left); integer(right)
        if relation == '=':
            valid = left == right
        elif relation == '<':
            valid = left < right
        elif relation == '<=':
            valid = left <= right
        else:
            raise ValueError('unsupported exact comparison')
        require(valid, 'exact arithmetic failed: ' + name)
        checks[name] = {'left': left, 'relation': relation, 'right': right}
    d = 1 << 42; h = 14409429; j = 97*h + 336; P = factorial(3)**2 * (1 << 16)
    m = monomials(); g = m['geometry_gamma']; f = m['fejer_x']
    for name, actual, expected in [
        ('P1',factorial(1)**2*2**4,16), ('P2',factorial(2)**2*2**9,2048),
        ('P3',P,2359296), ('W1_outer_exponent_label',40*1**3+1,41),
        ('W2_outer_exponent_label',40*2**3+1,321),
        ('W3_outer_exponent_label',40*3**3+1,1081),
        ('theta_coefficient',-g['theta'][0],59), ('theta_degree',g['theta'][1],176),
        ('theta_one_coefficient',-g['theta_one'][0],620025),
        ('theta_one_degree',g['theta_one'][1],1843952),
        ('spectrum_coefficient',g['q_bound'][0],620143),
        ('spectrum_degree',-g['q_bound'][1],1844304),
        ('rounded_radius_coefficient',155+4*18,227),
        ('rounded_radius_degree',32*18,576),
        ('g_coefficient',-g['g'][0],284), ('g_degree',g['g'][1],1408),
        ('beta_coefficient',-f['beta'][0],865346),
        ('beta_degree',-f['beta'][1],12362*(d+2)),
        ('t_coefficient',-f['t'][0],1730290),
        ('t_degree',-f['t'][1],24718*(d+2)),
        ('frequency_j',j,1397714949),
        ('frequency_degree',64*j+15*h+5153,89669903324),
        ('frequency_ceiling_coefficient',1+175+63*79,5153),
        ('quadratic_E_degree',12380*2048+24744,25378984),
        ('density_denominator',512*5**3,64000),
        ('interval_count',512*5**2+1,12801),
        ('uniformity_degree',2**(5-1),16),
        ('density_coefficient_degree',1+16*16,257),
        ('density_absorbed_degree',257+80,337),
        ('iteration_Q_coefficient',2*16,32),
        ('paper_label',2**(5+9),16384),
        ('square_first_inverse_f_coefficient',2,2),
        ('square_second_inverse_fg_coefficient',4*1,4),
        ('square_second_log_c_coefficient',4//2,2),
        ('square_second_inverse_f_coefficient',4*2//2,4),
    ]: check(name,actual,'=',expected)
    for name,left,relation,right in [
        ('Q_absorption',2**20+2**21,'<',2**22),
        ('q_bound_absorption',620143+1844304,'<',2**22),
        ('theta_one_absorption',620025+1843952,'=',2463977),
        ('d0_absorption',620025+1843952+8,'=',2463985),
        ('d0_degree_limit',2463985,'<',2**22),
        ('d_degree_limit',2**22+1,'<',2**32),
        ('u_inverse_absorption',4+2**22+2*2463977,'<',2**24),
        ('f_inverse_absorption',100+448,'=',548),
        ('g_inverse_absorption',284+1408,'=',1692),
        ('W_absorption',135+704,'=',839),
        ('K_absorption',114+320,'=',434),
        ('k_ceiling_absorption',434+1,'=',435),
        ('c_bracket_coefficient',228//2+576,'=',690),
        ('c_bracket_power',690,'<=',2**10),
        ('c_log_degree',434+11+1,'=',446),
        ('z_log_degree',435+11+1,'=',447),
        ('all_primitive_degrees',max(2**24,548,1692,839,446,447,2**22+1),'<',2**32),
        ('B_minimum_degree_suffices',9,'<',2**32),
        ('B_minimum_exceeds_323',323,'<',2**9),
        ('recurrence_shift_323',321+2,'=',323),
        ('recurrence_12B_coefficient',11+1,'=',12),
        ('recurrence_13B_coefficient',12+1,'=',13),
        ('threshold_15B_coefficient',13+2,'=',15),
        ('ceiling_16B_coefficient',15+1,'=',16),
        ('square_polynomial_coefficient',5+6//2,'=',8),
        ('square_polynomial_absorption_seed',5*4**2+6*4,'<=',2**(2*4)),
        ('geometric_D',4207554485+1,'<',2**32),
        ('geometric_B_degree',2**32*2**32,'=',2**64),
        ('geometric_log_degree',2**64+4,'<',2**65),
        ('frequency_degree_limit',89669903324,'<',2**37),
        ('frequency_first_branch',j+80,'<',89669903324),
        ('frequency_log_degree',37+1,'=',38),
        ('beta_absorption',865346+12362*(d+2),'=',54368650971157718),
        ('beta_degree_limit',54368650971157718,'<',2**56),
        ('t_absorption',1730290+24718*(d+2),'=',108710913663248398),
        ('t_degree_limit',108710913663248398,'<',2**57),
        ('sigma_constant',2*P,'<',2**23),
        ('sigma_small_sum_coefficient',23+2**58,'<',2**59),
        ('sigma_small_degree',59,'<',2**53),
        ('sigma_sum_degree',2**53+1,'<',2**54),
        ('Q_iter_log_degree',2**54+1,'<',2**55),
        ('iteration_ceiling_constant',9,'<=',2**4),
        ('iteration_ceiling_degree',2**56+4,'<',2**57),
        ('iteration_degree',2**57+2**55,'<',2**58),
        ('boundary_beta_coefficient',16*2**56,'=',2**60),
        ('boundary_small_sum',96+2**61,'<',2**62),
        ('boundary_outer_add',62+1,'=',63),
        ('boundary_c_log_degree',63+2,'=',65),
        ('phase_count_coefficient',2*8*12,'=',192),
        ('phase_count_dyadic',192,'<',2**8),
        ('phase_log_B0_degree',2**41+9,'<',2**42),
        ('P3_degree_limit',P,'<',2**22),
        ('phase_small_product_degree',22+59,'=',81),
        ('phase_max_degree',1081+1,'=',1082),
        ('phase_C_degree',1082+1,'=',1083),
        ('phase_C_localization_degree',1084,'<',2**54),
        ('quadratic_L2_other_dyadic_degree',4*2048,'=',8192),
        ('quadratic_L2_other_constant_degree',2*2048,'=',4096),
        ('quadratic_L2_dominance_label',14,'<',321),
        ('quadratic_L2_other_bound',8192,'<',2**14),
        ('quadratic_a_degree',25378984*(d+72),'<',2**68),
        ('quadratic_loglog_degree',323+1,'=',324),
        ('quadratic_localization_degree',324,'<',2**53),
        ('local_threshold_common_degree',2**55,'<',2**65),
        ('extra_interval_constant',12801,'<',2**14),
        ('iteration_A_degree',2**65+1,'<',2**66),
        ('final_loglog_degree',2**66+2,'<',2**67),
        ('density_constant',64000,'<',2**16),
        ('density_strict_degree',337,'<',2**9),
        ('density_final_degree',337*2**67,'<',2**76),
        ('paper_strict_degree_labels',76,'<',16384),
    ]: check(name,left,relation,right)
    return checks


def symbolic_certificate():
    return {
        'schema_version': 1, 'report': 298, 'commit': COMMIT,
        'proof_sha256': PROOF_SHA256,
        'pair_convention': '[u,v] denotes 2^u times gamma^v or x^v as labeled',
        'monomials': monomials(), 'formulas': formula_ledger(),
        'integer_checks': integer_checks(),
        'tower_policy': 'Only exponent labels and bounded integer coefficients are evaluated. No threshold, tower, real-power or floating-point values are evaluated.',
        'scope': 'Finite symbolic identities and sufficient integer inequalities only; the full real-variable proof is in provenance/PROOF.md and Report298.tex.',
    }


def canonical_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n').encode('utf-8')


def _reject_float(value):
    raise ValueError('noninteger JSON numeric literal forbidden')


def _parse_int(value):
    if len(value.lstrip('-')) > 40:
        raise ValueError('oversized JSON integer')
    return integer(int(value), 'JSON integer')


def _pairs(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError('duplicate JSON key')
        result[key] = value
    return result


def _identity(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_nlink, info.st_size,
            info.st_mtime_ns, info.st_ctime_ns)


def read_bounded(path):
    """Read only, with no-follow descriptors for every ancestor and the leaf."""
    if (os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW')
            or not hasattr(os, 'O_DIRECTORY') or os.open not in os.supports_dir_fd):
        raise RuntimeError('POSIX no-follow directory handles required')
    raw = str(path); path = Path(path)
    if (not path.is_absolute() or raw.startswith('//') or '\x00' in raw
            or any(p in ('.', '..') for p in raw.split('/'))):
        raise ValueError('ordinary absolute data path required')
    descriptor = os.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    fd = None
    try:
        for component in path.parts[1:-1]:
            child = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                            dir_fd=descriptor)
            os.close(descriptor); descriptor = child
        before = os.stat(path.name, dir_fd=descriptor, follow_symlinks=False)
        if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1 or before.st_size > MAX_BYTES:
            raise ValueError('bounded non-aliased regular data file required')
        fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                     dir_fd=descriptor)
        opened = os.fstat(fd)
        if _identity(before) != _identity(opened):
            raise ValueError('data file changed before read')
        data = bytearray()
        while True:
            chunk = os.read(fd, min(65536, MAX_BYTES + 1 - len(data)))
            if not chunk:
                break
            data.extend(chunk)
            if len(data) > MAX_BYTES:
                raise ValueError('data byte limit exceeded')
        after = os.fstat(fd)
        named = os.stat(path.name, dir_fd=descriptor, follow_symlinks=False)
        if _identity(before) != _identity(after) or _identity(after) != _identity(named) or len(data) != after.st_size:
            raise ValueError('data file changed during read')
        return bytes(data)
    finally:
        if fd is not None:
            os.close(fd)
        os.close(descriptor)


def parse_json_bytes(data):
    """Parse only an immutable bounded byte value; never reopen a data path."""
    if type(data) is not bytes or len(data) > MAX_BYTES:
        raise ValueError('immutable bounded JSON bytes required')
    if data.count(b'{') + data.count(b'[') > 4096:
        raise ValueError('JSON container limit exceeded')
    try:
        value = json.loads(data.decode('utf-8'), object_pairs_hook=_pairs,
                           parse_float=_reject_float, parse_constant=_reject_float, parse_int=_parse_int)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as error:
        raise ValueError('invalid bounded JSON') from error
    pending = [(value, 0)]; nodes = 0
    while pending:
        item, depth = pending.pop(); nodes += 1
        if depth > 16 or nodes > 20000:
            raise ValueError('JSON depth or node limit exceeded')
        children = item.values() if type(item) is dict else item if type(item) is list else ()
        pending.extend((child, depth+1) for child in children)
    if data != canonical_bytes(value):
        raise ValueError('canonical JSON required')
    return value


def load_json(path):
    """Bounded structural loader for diagnostics; no package pin is implied."""
    return parse_json_bytes(read_bounded(path))


def pinned_bytes(root, relative):
    """Read once and bind the package hash check to the exact returned bytes."""
    data = read_bounded(root / relative)
    require(hashlib.sha256(data).hexdigest() == DATA_PINS[relative],
            'bundled data pin mismatch: ' + relative)
    return data


def validate_certificate(value):
    expected = symbolic_certificate()
    if type(value) is not dict or value != expected or canonical_bytes(value) != canonical_bytes(expected):
        raise ValueError('certificate differs from recomputed exact ledger')
    return True


def verify_source_records(root=ROOT):
    """Verify pinned source metadata from the same byte snapshots that were hashed."""
    manifest_bytes = pinned_bytes(root, 'SOURCE_MANIFEST.json')
    excerpt_bytes = pinned_bytes(root, 'source_excerpts.json')
    return validate_source_records(parse_json_bytes(manifest_bytes),
                                   parse_json_bytes(excerpt_bytes))


def validate_source_records(manifest, excerpts):
    """Structural validation of parsed records; no reads and no pin check here."""
    require(manifest['commit'] == excerpts['commit'] == COMMIT, 'source commit mismatch')
    full = {entry['repository_path']: entry for entry in manifest['sources']}
    require(len(full) == len(manifest['sources']) == 50, 'full-file record inventory')
    for path, entry in full.items():
        require(type(path) is str and path.startswith('Combinatorics/Ramsey/') and '..' not in path.split('/'), 'repository path')
        require(entry['commit'] == COMMIT and type(entry['bytes']) is int and 0 < entry['bytes'] < 2**24, 'full-file metadata')
        require(re.fullmatch('[0-9a-f]{64}', entry['sha256']) is not None, 'full-file SHA256 format')
        require(re.fullmatch('[0-9a-f]{40}', entry['git_blob_sha1']) is not None, 'Git blob format')
        require(entry['url'] == 'https://github.com/VladimirReshetnikov/ProveIt/blob/' + COMMIT + '/' + path, 'source URL')
    names = set(); line_count = 0
    for entry in excerpts['excerpts']:
        require(entry['name'] not in names, 'duplicate excerpt name'); names.add(entry['name'])
        text = entry['text']
        require(type(text) is str and text.endswith('\n'), 'excerpt text format')
        require(hashlib.sha256(text.encode('utf-8')).hexdigest() == entry['excerpt_sha256'], 'excerpt hash mismatch')
        require(entry['repository_path'] in full, 'excerpt missing full-file identity')
        source = full[entry['repository_path']]
        require(entry['source_sha256'] == source['sha256'], 'excerpt full-file hash link')
        start, end = entry['start_line'], entry['end_line']
        require(type(start) is int and type(end) is int and 1 <= start <= end <= 100000, 'excerpt line range')
        require(len(text.splitlines()) == end-start+1, 'excerpt line count')
        require(entry['url'] == source['url'] + '#L' + str(start) + '-L' + str(end), 'excerpt source link mismatch')
        line_count += end-start+1
    require(len(names) == 56 and line_count == 171, 'excerpt exact inventory')
    required = {'natural_five_term_fejer','HasNatAP',
                'section13DensityRecurrenceThreshold','section13DensityIntegerThreshold',
                'section13GeometricThreshold','squareScaleThreshold','squarePowerThreshold',
                'densityIterationClosedThreshold','theorem_18_2'}
    require(required <= names, 'required source branch absent')
    spans = excerpts['paper_formula_spans']
    require(len(spans) == 2 and {e['name'] for e in spans} ==
            {'paper_right_association_formula','paper_theorem_18_2_tower'}, 'paper formula inventory')
    for entry in spans:
        source = full[entry['repository_path']]
        require(entry['source_sha256'] == source['sha256'], 'paper full-file hash link')
        text = entry['text']
        require(type(text) is str and '\n' not in text and len(text) < 100, 'paper math span format')
        require(hashlib.sha256(text.encode('utf-8')).hexdigest() == entry['span_sha256'], 'paper span hash mismatch')
        line, start, end = entry['source_line'], entry['start_byte_zero_based'], entry['end_byte_exclusive']
        require(type(line) is int and line in (3838,3840), 'paper source line')
        require(type(start) is int and type(end) is int and 0 <= start < end <= 1000, 'paper span range')
        require(end-start == len(text.encode('utf-8')), 'paper span byte count')
        require(entry['url'] == source['url'] + '#L' + str(line), 'paper source URL')
    return {'full_file_identity_records': len(full), 'excerpt_records': len(names),
            'paper_math_spans': len(spans),
            'excerpt_lines': line_count, 'full_files_bundled': False,
            'full_files_refetched_or_authenticated_by_this_run': False,
            'excerpt_to_complete_file_match_rechecked_by_this_run': False,
            'full_source_dependencies_compiled': False}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    try:
        expected_paths = {'companion/certificate.json','SOURCE_MANIFEST.json',
                          'source_excerpts.json','provenance/PROOF.md'}
        require(set(DATA_PINS) == expected_paths, 'exact data pin inventory')
        # Snapshot immutable bytes once. Every subsequent parse uses these same
        # checked bytes, even if the filesystem changes after an individual read.
        snapshot = {relative: pinned_bytes(ROOT, relative) for relative in DATA_PINS}
        require(DATA_PINS['provenance/PROOF.md'] == PROOF_SHA256, 'frozen proof identity')
        cert = parse_json_bytes(snapshot['companion/certificate.json'])
        validate_certificate(cert)
        output = {'report': 298, 'status': 'passed', 'integer_checks': len(integer_checks()),
                  'symbolic_monomials': sum(len(g) for g in monomials().values()),
                  'source_records': validate_source_records(
                      parse_json_bytes(snapshot['SOURCE_MANIFEST.json']),
                      parse_json_bytes(snapshot['source_excerpts.json'])),
                  'proof_sha256': PROOF_SHA256,
                  'tower_values_evaluated': False, 'float_values_used': False,
                  'scope': 'Offline bundled-data consistency, exact coefficient/exponent identities and sufficient integer checks only. The manuscript proves the inequalities for every real density; no finite sampling, Lean compilation, upstream execution, network access or full-file authentication is performed.'}
        sys.stdout.buffer.write(canonical_bytes(output))
        return 0
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
        parser.exit(1, 'ERROR: ' + str(error) + '\n')


if __name__ == '__main__':
    raise SystemExit(main())
