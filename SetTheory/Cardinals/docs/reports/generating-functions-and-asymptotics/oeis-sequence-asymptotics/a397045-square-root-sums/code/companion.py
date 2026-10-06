#!/usr/bin/env python3
"""Report172 exact checks and explicitly noncertified saddle diagnostics.

All count membership decisions use rational root enclosures. An unresolved
comparison raises ValidationError; floating point is used only by diagnostics.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
FIXTURE_SHA256 = '65f8d562a59ff6ce7f4f50ec620e5e7112aee683647c88c9972f3b3dedd65d24'

class ValidationError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise ValidationError(message)


def integer(value, name, minimum, maximum):
    require(type(value) is int and minimum <= value <= maximum,
            f'{name} must be an integer in [{minimum}, {maximum}]')
    return value


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + '\n').encode('utf-8')


def write_new(path, content):
    """Exclusive creation; never follows or replaces an existing destination."""
    require(isinstance(content, bytes), 'write_new content must be bytes')
    path = Path(path)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, 'O_NOFOLLOW'):
        flags |= os.O_NOFOLLOW
    fd = os.open(path, flags, 0o644)
    try:
        with os.fdopen(fd, 'wb') as handle:
            handle.write(content)
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def squarefree(d):
    integer(d, 'radicand', 1, 10**9)
    return all(d % (j*j) for j in range(2, math.isqrt(d)+1))


def root_bounds(d, bits=96):
    integer(d, 'radicand', 1, 10**9)
    integer(bits, 'bits', 1, 256)
    q = 1 << bits
    lo = math.isqrt(d*q*q)
    return lo, lo if lo*lo == d*q*q else lo+1


def load_fixture(directory=None):
    directory = Path(directory) if directory is not None else ROOT / 'fixtures'
    path = directory / 'oeis_35_historical.json'
    require(path.is_file() and not path.is_symlink(), 'fixture must be a regular, nonsymlink file')
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == FIXTURE_SHA256, 'historical fixture SHA-256 mismatch')
    checksums = json.loads((directory / 'SHA256.json').read_text())
    require(checksums == {'oeis_35_historical.json': FIXTURE_SHA256}, 'fixture checksum manifest mismatch')
    fixture = json.loads(raw)
    terms = fixture.get('terms', {})
    require(set(terms) == {str(n) for n in range(36)}, 'fixture must have exactly n=0,...,35')
    require(all(type(terms[str(n)]) is int and terms[str(n)] > 0 for n in range(36)), 'invalid fixture term')
    return {int(n): a for n, a in terms.items()}


def enumerate_sums(limit, include_unit=False, record=False, bits=96):
    """Count canonical sums in [0,limit); buckets are direct unit-width shells.

    The independent Python implementation uses trial-division squarefreeness
    and arbitrary-precision integers rather than the C++ sieve and uint64_t.
    No result is emitted on ambiguity.
    """
    integer(limit, 'limit', 1, 21)
    integer(bits, 'bits', 1, 256)
    require(type(include_unit) is bool and type(record) is bool, 'flags must be booleans')
    require(not record or limit <= 7, 'recording is limited to limit <= 7')
    q = 1 << bits
    roots = [(d, *root_bounds(d, bits))
             for d in range(1 if include_unit else 2, limit*limit) if squarefree(d)]
    buckets = [0]*limit
    records = []
    lower_distance = upper_distance = q
    def walk(start, lo, hi, seq):
        nonlocal lower_distance, upper_distance
        if lo >= limit*q:
            return
        floor = lo//q
        require(floor == hi//q, 'ambiguous integer boundary: increase enclosure precision')
        buckets[floor] += 1
        if lo != hi:
            lower_distance = min(lower_distance, lo % q)
            upper_distance = min(upper_distance, q-hi % q)
        if record:
            records.append(seq)
        for k in range(start, len(roots)):
            d, a, b = roots[k]
            if lo+a >= limit*q:
                break
            walk(k, lo+a, hi+b, seq+(d,) if record else ())
    walk(0, 0, 0, ())
    return buckets, records, {
        'vectors': sum(buckets), 'generators': len(roots),
        'minimum_lower_boundary_distance_numerator': lower_distance,
        'minimum_upper_boundary_distance_numerator': upper_distance,
        'distance_denominator': q, 'ambiguous_comparisons': 0}


def canonical_sequence(sequence):
    require(type(sequence) in (list, tuple), 'canonical sequence must be a list or tuple')
    require(len(sequence) <= 1000, 'canonical sequence too long')
    for d in sequence:
        integer(d, 'radicand', 1, 10**6)
        require(squarefree(d), 'endpoint radicands must be squarefree')
    return Counter(sequence)


def compare(left, right, bits=96):
    """Exact canonical equality or a separated rational difference enclosure."""
    integer(bits, 'bits', 1, 256)
    lc, rc = canonical_sequence(left), canonical_sequence(right)
    coefficients = {d: lc[d]-rc[d] for d in lc.keys() | rc.keys() if lc[d] != rc[d]}
    if not coefficients:
        return 0
    lo = hi = 0
    for d, multiplicity in coefficients.items():
        a, b = root_bounds(d, bits)
        lo += multiplicity*(a if multiplicity > 0 else b)
        hi += multiplicity*(b if multiplicity > 0 else a)
    if hi < 0:
        return -1
    if lo > 0:
        return 1
    raise ValidationError('ambiguous real endpoint: increase enclosure precision')


def endpoint_checks(bits=96):
    _, records, _ = enumerate_sums(7, record=True, bits=bits)
    result = []
    for endpoint in [(), (1,), (2,), (2,2), (2,3), (2,5), (1,)*3, (1,)*6]:
        signs = [compare(seq, endpoint, bits) for seq in records]
        strict, equality = signs.count(-1), signs.count(0)
        jump = int(not endpoint or all(d != 1 for d in endpoint))
        require(equality == jump, 'incorrect endpoint jump')
        result.append({'endpoint_radicands': endpoint, 'strict_count': strict,
                       'weak_count': strict+equality, 'atom_count': equality})
    return result


def exact(max_n=20, shell_n=12, bits=96):
    integer(max_n, 'max_n', 0, 20)
    integer(shell_n, 'shell_n', 0, min(max_n, 12))
    integer(bits, 'bits', 1, 256)
    fixture = load_fixture()
    raw, _, info = enumerate_sums(max_n+1, bits=bits)
    total = 0
    prefix = []
    for count in raw:
        total += count
        prefix.append(total)
    require(prefix == [fixture[n] for n in range(max_n+1)], 'cumulative prefix mismatch')
    shells, _, shell_info = enumerate_sums(shell_n+1, include_unit=True, bits=bits)
    require(shells == [fixture[n] for n in range(shell_n+1)], 'independent direct shell mismatch')
    return {'status':'PASS', 'scale_bits':bits, 'fresh_cumulative_max_n':max_n,
            'prefix':prefix, 'cumulative_run':info,
            'fresh_direct_shell_max_n':shell_n, 'direct_shells':shells,
            'direct_shell_run':shell_info, 'endpoint_checks':endpoint_checks(bits),
            'historical_fixture_max_n':35,
            'scope':'Fresh coverage is only the stated prefix. The historical n=35 run is not repeated here.',
            'arithmetic':'Arbitrary-precision integers and rational root enclosures; ambiguity aborts',
            'auxiliary_n0':'The zero-vector convention gives a(0)=1.',
            'source':'https://oeis.org/A397045'}


def cpp(max_n=20, allow_full=False, bits=48):
    integer(max_n, 'max_n', 0, 35)
    require(type(allow_full) is bool, 'allow_full must be boolean')
    integer(bits, 'bits', 1, 48)
    require(max_n <= 20 or allow_full, 'n>20 requires explicit --allow-full')
    fixture = load_fixture()
    with tempfile.TemporaryDirectory(prefix='report172-cpp-') as temp:
        binary = Path(temp)/'enumerate_roots'
        subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-pedantic',
                        str(ROOT/'code/enumerate_roots.cpp'),'-o',str(binary)], check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=120)
        result = subprocess.run([str(binary),str(max_n),str(bits)], check=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                timeout=3600 if allow_full else 120)
    report = json.loads(result.stdout)
    require(report['prefix'] == [fixture[n] for n in range(max_n+1)], 'C++ prefix mismatch')
    require(report['ambiguous_comparisons'] == 0, 'C++ ambiguous comparison')
    return report


# Decimal constants are rounded to binary64 only in the exploratory diagnostics.
ZETA3 = 1.202056903159594285399738161511449990764986292
A = 12*ZETA3/math.pi**2
K = 3*(A/4)**(1/3)


def diagnostics(ns=(5,10,20,35)):
    require(type(ns) in (list,tuple) and 1 <= len(ns) <= 20, 'ns must contain 1..20 integers')
    for n in ns:
        integer(n, 'diagnostic n', 1, 10000)
    fixture = load_fixture()
    results = []
    for n in ns:
        x = n+1
        t0 = (2*A/x)**(1/3)
        lower, upper = t0/2, t0*2
        dmax = math.ceil((32/lower)**2)
        sf = bytearray(b'\1')*(dmax+1)
        sf[:2] = b'\0\0'
        for j in range(2, math.isqrt(dmax)+1):
            for k in range(j*j,dmax+1,j*j):
                sf[k] = 0
        roots = [math.sqrt(d) for d in range(2,dmax+1) if sf[d]]
        def mean(t):
            return math.fsum(r/math.expm1(t*r) for r in roots)
        require(mean(lower) > x > mean(upper), 'numerical saddle bracket failed')
        for _ in range(64):
            middle = (lower+upper)/2
            if mean(middle) > x:
                lower = middle
            else:
                upper = middle
        t = (lower+upper)/2
        F = math.fsum(-math.log1p(-math.exp(-t*r)) for r in roots)
        v = math.fsum(r*r*math.exp(-t*r)/(-math.expm1(-t*r))**2 for r in roots)
        H = F+t*x-math.log(t)-math.log(2*math.pi*v)/2
        cutoff = math.sqrt(dmax)
        tail = 2*math.exp(-t*cutoff)*(cutoff/t+1/t**2)/(-math.expm1(-t*cutoff))
        require(math.isfinite(tail) and tail > 0, 'invalid positive log-product tail bound')
        item = {'n':n,'x':x,'t':t,'D':dmax,'F_truncated':F,'mean_truncated':mean(t),
                'variance_truncated':v,'log_saddle':H,'log_leading':K*x**(2/3),
                'positive_analytic_F_tail_bound_evaluated_in_binary64':tail}
        if n in fixture:
            item.update(log_exact=math.log(fixture[n]),
                        saddle_relative_error=math.expm1(H-math.log(fixture[n])),
                        exact_term_provenance='historical verified fixture; see separate fresh coverage')
        results.append(item)
    return {'status':'EXPLORATORY_NONCERTIFIED','A':A,'K':K,
            'disclaimer':'Binary64 arithmetic, finite product, and numerical bisection are not interval-certified. The positive analytic tail bound controls only omitted log-product terms; its floating evaluation, all rounding, derivatives, and the root solve are not certified. These are diagnostics, not finite-n error certificates.',
            'tail_bound':'0 < F(t)-F_D(t) <= 2 exp(-t sqrt(D)) (sqrt(D)/t + 1/t^2)/(1-exp(-t sqrt(D))). This follows by enlarging squarefree d>D to every integer and integrating the decreasing exponential.',
            'results':results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('exact', help='fresh independent Python checks; at most n=20')
    p.add_argument('--n',type=int,default=20)
    p.add_argument('--shell-n',type=int,default=12)
    p.add_argument('--bits',type=int,default=96)
    p = sub.add_parser('cpp', help='C++ enclosure enumeration; n>20 explicitly opt-in')
    p.add_argument('--n',type=int,default=20)
    p.add_argument('--bits',type=int,default=48)
    p.add_argument('--allow-full',action='store_true')
    p = sub.add_parser('diagnostics', help='noncertified exact-product saddle diagnostics')
    p.add_argument('--n',type=int,nargs='+',default=[5,10,20,35])
    for p in sub.choices.values():
        p.add_argument('--output',type=Path,help='new JSON path; never overwritten')
    args = parser.parse_args()
    try:
        if args.output:
            require(not args.output.exists() and not args.output.is_symlink(), 'refusing existing output')
            require(args.output.parent.is_dir(), 'output parent must exist')
        if args.command == 'exact':
            result = exact(args.n,args.shell_n,args.bits)
        elif args.command == 'cpp':
            result = cpp(args.n,args.allow_full,args.bits)
        else:
            result = diagnostics(args.n)
        data = json_bytes(result)
        if args.output:
            write_new(args.output,data)
        else:
            sys.stdout.write(data.decode())
    except (ValueError,OSError,subprocess.SubprocessError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 2
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
