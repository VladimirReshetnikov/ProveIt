#!/usr/bin/env python3
"""Offline exact identities and bounded regressions; not a real-inequality prover."""
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
import stat

ROOT = Path(__file__).absolute().parents[1]
COMMIT = 'af74fb522c24a6331886b11db76942642a6a0e42'
MAX_BYTES = 128 * 1024
MAX_INT = 1 << 120
DATA_PINS = {
    'companion/certificate.json': '0205047aed6fcb0fa66175525f641153049c35b15680122d78253f9d87815a52',
    'SOURCE_MANIFEST.json': '43653bec3a52993f800bfbaec4b5af562e06618cbbad4aaae0b3a91987a6d9de',
    'source_excerpts.json': '4ef414cdb2b0bef47d90f8dca6d666c02631c9a023b51c9bb24ce242972ede34',
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def integer(value, name='integer', bound=MAX_INT):
    if type(value) is not int or abs(value) > bound:
        raise ValueError(name + ' must be a bounded exact integer')
    return value


def pair(value):
    if type(value) is not tuple or len(value) != 2:
        raise ValueError('monomial must be an exponent pair tuple')
    return tuple(integer(v, 'exponent') for v in value)


def multiply(left, right):
    a, b = pair(left), pair(right)
    return pair((a[0] + b[0], a[1] + b[1]))


def power(value, exponent):
    a = pair(value)
    integer(exponent, 'monomial power', 30000)
    return pair((a[0] * exponent, a[1] * exponent))


def quotient(left, right):
    a, b = pair(left), pair(right)
    return pair((a[0] - b[0], a[1] - b[1]))


def monomials(d):
    integer(d, 'density exponent')
    if not 1 <= d <= (1 << 88):
        raise ValueError('density exponent outside diagnostic range')
    a = (-71 - d, 2 + d)
    mu = (-59 - d, 2 + d)
    half_a = multiply(a, (-1, 0))
    b = multiply(multiply((-20, 0), power(a, 2)), power(half_a, 12359))
    s = multiply((-26, 0), power(half_a, 24718))
    t = multiply(s, (-4, 0))
    beta = multiply(multiply(mu, b), (-1, 0))
    return dict(a=a, mu=mu, b=b, s=s, t=t, beta=beta)


def rational(value, name='rational'):
    if type(value) is int:
        value = Fraction(integer(value))
    if type(value) is not Fraction:
        raise ValueError(name + ' must be an exact integer or Fraction')
    integer(value.numerator); integer(value.denominator)
    return value


def ceil_positive(value):
    value = rational(value)
    if value <= 0:
        raise ValueError('positive ceiling argument required')
    return (value.numerator + value.denominator - 1) // value.denominator


def iteration_case(af, ao, qf, qo, nf, no, gain):
    af, ao, qf, qo, gain = [rational(v) for v in (af, ao, qf, qo, gain)]
    integer(nf, 'new count', 128); integer(no, 'old count', 128)
    if not (0 < af < ao and 0 < qf and qo > 1 and gain >= 1
            and qf <= qo / gain and 1 <= nf <= no):
        raise ValueError('iteration comparison hypotheses not satisfied')
    left = af * qf ** nf
    right = ao * qo ** no / gain ** nf
    require(left < right, 'exact iteration comparison failed')
    return left, right


def symbolic_certificate():
    do, df, ro, rf = 2**76, 2**42, 2**88, 2**53
    delta = do - df
    old, new = monomials(do), monomials(df)
    ratios = {k: list(quotient(new[k], old[k])) for k in ('a', 'mu', 't', 'beta')}
    require(ratios['a'] == [delta, -delta], 'a ratio identity')
    require(ratios['mu'] == [delta, -delta], 'mass ratio identity')
    require(ratios['t'] == [24718*delta, -24718*delta], 't ratio identity')
    require(ratios['beta'] == [12362*delta, -12362*delta], 'beta ratio identity')
    constants = {
        'quadratic_degree': 2 + 12359,
        'quadratic_size_degree': 2 * 12359,
        'quadratic_size_two_loss': 14 + 12,
        'local_count_two_loss': 14 + 12 + 4,
        'partition_P3': factorial(3)**2 * 2**16,
        'quadratic_threshold_exponent': 12380 * 2048 + 24744,
        'density_denominator': 512 * 5**3,
        'interval_count_constant': 512 * 5**2 + 1,
        'uniformity_exponent': 2**(5-1),
        'localization_gain_floor': 2**2,
        'phase_loss': 12,
        'phase_absorption_cube': 4**3,
        'iteration_Q_numerator': 2 * 16,
    }
    expected = [12361, 24718, 26, 30, 2359296, 25378984, 64000, 12801, 16, 4, 12, 64, 32]
    require(list(constants.values()) == expected, 'integer constant reduction')
    require(ro >= rf + 1 and rf >= 1 and do > df, 'ordered source exponents')
    require(12 < 4**3, 'strict phase absorption')
    require(0 < Fraction(1, constants['partition_P3']) <= 1, 'partition inverse bound')
    return dict(schema_version=1, commit=COMMIT, constants=constants,
                source_exponents=dict(d_old=do, d_fejer=df, r_old=ro, r_fejer=rf),
                delta=delta, monomials_old={k:list(v) for k,v in old.items()},
                monomials_fejer={k:list(v) for k,v in new.items()}, ratio_pairs=ratios,
                scope='Exact monomial and integer identities only; continuous inequalities are proved in Report296.tex')


def regressions():
    betas = sorted({Fraction(a, d) for d in range(2, 13) for a in range(1, d)})
    counts = dict(ceiling_cases=0, equal_ceiling_cases=0, coefficient_cases=0,
                  maximum_cases=0, shared_maximum_cases=0, iteration_cases=0)
    for bo in betas:
        for bf in betas:
            if bo >= bf:
                continue
            no, nf = ceil_positive(8/bo), ceil_positive(8/bf)
            require(1 <= nf <= no, 'ceiling monotonicity regression')
            counts['ceiling_cases'] += 1
            counts['equal_ceiling_cases'] += int(nf == no)
            for bold, bnew in ((4, 4), (8, 4), (16, 8)):
                co, cf = bo/(8*bold), bf/(8*bnew)
                require(0 < co < cf < 1, 'coefficient monotonicity regression')
                counts['coefficient_cases'] += 1
    for common in (1, 8, 100):
        for old in (2, 4, 16):
            for new in (1, 2):
                require(max(common, new) <= max(common, old), 'shared maximum regression')
                counts['maximum_cases'] += 1
                counts['shared_maximum_cases'] += int(common >= old and common >= new)
    for nf in range(1, 17):
        for gap in range(5):
            for gain in (4, 5, 8):
                for qf in (64, 128):
                    iteration_case(Fraction(3, 2), Fraction(7, 3), qf, qf*gain,
                                   nf, nf+gap, gain)
                    counts['iteration_cases'] += 1
    require(counts['equal_ceiling_cases'] > 0 and counts['shared_maximum_cases'] > 0,
            'degenerate equality branches were not exercised')
    return counts


def canonical_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n').encode('utf-8')


def _reject_float(value):
    raise ValueError('noninteger JSON numeric literal forbidden')


def _parse_int(value):
    if len(value.lstrip('-')) > 100:
        raise ValueError('oversized JSON integer')
    return integer(int(value), 'JSON integer')


def _pairs(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError('duplicate JSON key')
        result[key] = value
    return result


def read_bounded(path):
    path = Path(path)
    before = path.lstat()
    if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1 or before.st_size > MAX_BYTES:
        raise ValueError('bounded non-aliased regular data file required')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        opened = os.fstat(fd)
        if (before.st_dev, before.st_ino) != (opened.st_dev, opened.st_ino):
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
        fields = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_nlink)
        if fields(before) != fields(after) or fields(after) != fields(path.lstat()):
            raise ValueError('data file changed during read')
        return bytes(data)
    finally:
        os.close(fd)


def load_json(path):
    data = read_bounded(path)
    if data.count(b'{') + data.count(b'[') > 2048:
        raise ValueError('JSON container limit exceeded')
    try:
        value = json.loads(data.decode('utf-8'), object_pairs_hook=_pairs,
                           parse_float=_reject_float, parse_constant=_reject_float, parse_int=_parse_int)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as error:
        raise ValueError('invalid bounded JSON') from error
    pending = [(value, 0)]; nodes = 0
    while pending:
        item, depth = pending.pop(); nodes += 1
        if depth > 16 or nodes > 10000:
            raise ValueError('JSON depth or node limit exceeded')
        children = item.values() if type(item) is dict else item if type(item) is list else ()
        pending.extend((child, depth + 1) for child in children)
    if data != canonical_bytes(value):
        raise ValueError('canonical JSON required')
    return value


def validate_certificate(value):
    if type(value) is not dict or value != symbolic_certificate():
        raise ValueError('certificate differs from recomputed exact identities')
    # Equality in Python identifies True with 1; canonical bytes deliberately do not.
    if canonical_bytes(value) != canonical_bytes(symbolic_certificate()):
        raise ValueError('certificate types differ from exact schema')
    return True


def verify_source_records(root=ROOT):
    manifest = load_json(root / 'SOURCE_MANIFEST.json')
    excerpts = load_json(root / 'source_excerpts.json')
    require(manifest['commit'] == excerpts['commit'] == COMMIT, 'source commit mismatch')
    full = {e['repository_path']: e for e in manifest['sources']}
    require(len(full) == len(manifest['sources']) == 34, 'full-file record inventory')
    names = set()
    line_count = 0
    for entry in excerpts['excerpts']:
        require(entry['name'] not in names, 'duplicate excerpt name')
        names.add(entry['name'])
        text = entry['text']
        require(type(text) is str and text.endswith('\n'), 'excerpt text format')
        require(hashlib.sha256(text.encode()).hexdigest() == entry['excerpt_sha256'], 'excerpt hash mismatch')
        require(entry['repository_path'] in full, 'excerpt missing full-file identity')
        start, end = entry['start_line'], entry['end_line']
        require(type(start) is int and type(end) is int and 1 <= start <= end, 'excerpt line range')
        require(len(text.splitlines()) == end-start+1, 'excerpt line count')
        expected_url = full[entry['repository_path']]['url'] + '#L' + str(start) + '-L' + str(end)
        require(entry['url'] == expected_url, 'excerpt source link mismatch')
        line_count += end-start+1
    require(len(names) == 48 and line_count == 133, 'excerpt exact inventory')
    require('natural_five_term_fejer' in names and 'HasNatAP' in names, 'progression interface absent')
    return dict(full_file_identity_records=len(full), excerpt_records=len(names), excerpt_lines=line_count,
                full_files_refetched=False, full_source_dependencies_compiled=False)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    try:
        for relative, digest in DATA_PINS.items():
            require(hashlib.sha256(read_bounded(ROOT / relative)).hexdigest() == digest,
                    'bundled data pin mismatch: ' + relative)
        require(set(DATA_PINS) == {'companion/certificate.json', 'SOURCE_MANIFEST.json', 'source_excerpts.json'},
                'exact data pin inventory')
        validate_certificate(load_json(ROOT / 'companion/certificate.json'))
        output = dict(report=296, status='passed', symbolic_identities='exact',
                      source_records=verify_source_records(), regressions=regressions(),
                      scope='Finite exact diagnostics only; the manuscript proves all real-density inequalities')
        sys.stdout.buffer.write(canonical_bytes(output))
        return 0
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
        parser.exit(1, 'ERROR: ' + str(error) + '\n')


if __name__ == '__main__':
    raise SystemExit(main())
