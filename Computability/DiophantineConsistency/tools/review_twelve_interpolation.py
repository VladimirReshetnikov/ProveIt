#!/usr/bin/env python3
"""Read-only provenance and independent local checks for the twelve-Z arrival.

The supplied release is replayed separately in two full scratch copies.  This
tool imports no arrival code, invokes no compiler, and does not modify any
arrival member.  Finite Pell controls are arithmetic regression tests, not a
proof of a universal calibration theorem or a consistency experiment.
"""
import argparse
import gzip
import hashlib
import importlib.util
import json
import sys
from math import gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location(
    'interpolation_review_ring',
    ROOT / 'candidates/positive11-adaptive-shears/independent_ring.py')
RING = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RING)
Ring = RING.Ring
ARCHIVE_SHA = 'f44b903de17a70316787ff57562a3d8fe3bdec12791e266318cedb49e7125f72'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pell(a, n, modulus=None):
    """Return chi_a(n), psi_a(n), by binary unit powering."""
    need(n >= 0, 'nonnegative Pell index')
    delta = a*a-1
    def mul(p, q):
        x, y = p; z, w = q
        out = x*z+delta*y*w, x*w+y*z
        return tuple(v % modulus for v in out) if modulus else out
    out = (1, 0); power = (a, 1)
    while n:
        if n & 1:
            out = mul(out, power)
        power = mul(power, power)
        n //= 2
    return out


def valuation(n, p):
    need(n != 0, 'finite valuation')
    v = 0
    while n % p == 0:
        n //= p; v += 1
    return v


def prime_divisors(n):
    out = []; p = 2
    while p*p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def crt(a, m, b, n):
    """The least nonnegative generalized-CRT solution and its period."""
    g = gcd(m, n)
    need((b-a) % g == 0, 'CRT compatibility')
    r = n//g
    step = (((b-a)//g)*pow(m//g, -1, r)) % r if r > 1 else 0
    period = m*r
    return (a+m*step) % period, period


def local_identities():
    u, D, H, x = [Ring.variable(n) for n in ('u', 'D', 'H', 'x')]
    q0 = u*u+D+31*H*H
    c0 = u*(u*u+3*D+H*H)+H**3
    c1 = 3*u*u+D+H*H
    A = q0*c0+2*u*D*c1
    B = q0*c1+2*u*c0
    need(A == u**5+10*u**3*D+5*u*D**2+32*H**2*(u**3+3*u*D)
         +H**3*(u*u+D)+31*H**4*u+31*H**5, 'literal quintic even part')
    need(B == 5*u**4+10*u*u*D+D*D+32*H*H*(3*u*u+D)
         +2*H**3*u+31*H**4, 'literal quintic odd part')
    need(B == 5*u**4+10*u*u*D+D*D+32*H*H*D+95*H*H*u*u
         +H*H*(u+H)**2+30*H**4, 'strictly positive B decomposition')
    need(5*x**4+96*x*x+2*x+31 ==
         5*x**4+95*x*x+(x+1)**2+30, 'positive derivative identity')

    a, c, s, r, T, rank, f = [Ring.variable(n) for n in ('a', 'c', 's', 'r', 'T', 'rank', 'f')]
    delta = a*a+4*a+3; I = s*r*c*c; Df = 1+delta*I*I
    b = c-rank+4*I*T; V = Df*b-c
    j_aux = delta*s*s*r*r*c**3*(c-rank)+4*s*r*c*Df*T
    need(c*j_aux-rank == V, 'integer auxiliary quotient restoration')
    need(f*(f*b)-c-V == (f*f-Df)*b, 'first auxiliary quotient remainder')

    M, q, gamma, b0, ss, ff, tau, g, y, VV = [Ring.variable(n) for n in
        ('M', 'q', 'gamma', 'b0', 'ss', 'ff', 'tau', 'g', 'y', 'VV')]
    U = M*H
    v = q*q+M*ss
    n = gamma+ff+tau+g+y-VV-ss
    Z = U*(n+VV)+M*b0+H*(v-q*q)
    need(Z == M*(b0+H*gamma)+U*(ff+tau+g+y), 'trace-carrier inverse identity')

    # Work in the norm-one algebra z^2=f^2-1; no division is used.
    def unit_mul(p, q):
        return (p[0]*q[0]+(f*f-1)*p[1]*q[1], p[0]*q[1]+p[1]*q[0])
    alpha2 = unit_mul((f, Ring.numeral(1)), (f, Ring.numeral(1)))
    alpha4 = unit_mul(alpha2, alpha2)
    need(alpha4[0]-(1-4*f*f) == 4*f*f*(2*f*f-1), 'squared-modulus period constant')
    need(alpha4[1]+4*f == 8*f**3, 'squared-modulus period radical coefficient')

    # The exact odd Chebyshev identity, independently of any supplied code.
    AA = Ring.variable('AA'); Delta = AA*AA-1
    Qprev, Qcurr = Ring.numeral(1), 4*(1-AA*AA)-3
    Uprev, Ucurr = Ring.numeral(1), 4*AA*AA-1
    need(Qprev == Uprev and Qcurr == -Ucurr, 'initial odd Chebyshev substitution')
    for m in range(1, 13):
        Qnext = (2-4*AA*AA)*Qcurr-Qprev
        Unext = (4*AA*AA-2)*Ucurr-Uprev
        need(Qnext == ((-1)**(m+1))*Unext, 'odd Chebyshev substitution')
        Qprev, Qcurr = Qcurr, Qnext
        Uprev, Ucurr = Ucurr, Unext

    return {'exact_identities': [
        'quintic even and odd quadratic remainder', 'strictly positive odd coefficient',
        'strictly positive derivative', 'two literal auxiliary coordinate formulas',
        'trace-carrier completeness', 'two norm-one period coordinates',
        'odd Chebyshev substitution through degree27'],
        'boundary': 'Exact local identities; universal lifting, trace and calibration arguments are reviewed in prose.'}


def arithmetic_controls():
    homogeneity = 0
    for H in range(-24, 25):
        if H == 0:
            continue
        for x in range(-64, 65):
            phi = x**5+32*H*H*x**3+H**3*x*x+31*H**4*x+31*H**5
            if phi % H**5 == 0:
                need(x % H == 0, 'homogeneous divisibility finite control')
            homogeneity += 1

    lifting = 0; even = 0; index_multiple = 0
    for a in range(2, 15, 2):
        for m in range(1, 81):
            f, I = pell(a, m)
            need(f*f-(a*a-1)*I*I == 1 and gcd(f, I) == 1, 'Pell norm and coprimality')
            for p in prime_divisors(m):
                if I % p == 0:
                    need(valuation(I, p) >= valuation(m, p), 'index valuation finite control')
                    lifting += 1
            if m % 2 == 0:
                need(valuation(I, 2) == valuation(m, 2)+valuation(a, 2), 'even-base 2-adic exact control')
                need(gcd(4*m*f, 4*I*I) <= 4*I and (4*I) % gcd(4*m*f, 4*I*I) == 0,
                     'all-class CRT gcd control')
                even += 1
        for p in range(1, 12):
            cp, sp = pell(a, p)
            for k in range(1, 12):
                unused, sk = pell(a, p*k)
                need((sk-k*pow(cp, k-1)*sp) % (sp*sp) == 0, 'strong-index binomial control')
                index_multiple += 1

    # A genuinely false shortened period is rejected, not merely sampled.
    need(pell(2, 8, 49) == (1, 35), 'explicit false 4m period example')
    need(pell(2, 56, 49) == (1, 0), 'corrected 4mf period example')

    # Exact congruence fixtures, including a full c²-divisible strong witness.
    # Only modular Pell coordinates are formed, never the gigantic witness V0.
    fixtures = []
    for a, R, m, classes in [(2, 3, 2, range(4)),
                              (2, 3, 180, [-2, -1, 0, 1, 2])]:
        delta = a*a-1; unused, c = pell(a, R); f, I = pell(a, m)
        lam = 4*m*f; g = gcd(lam, 4*I*I)
        need((4*I) % g == 0 and c % 4 == R % 4 and f % 2 == 1,
             'fixture preconditions')
        if m == 180:
            need(I % (4*c*c) == 0, 'fixture full c² divisibility')
        rho = delta*I
        for residue in classes:
            ell, period = crt(R, lam, R-4*I*residue, 4*I*I)
            if ell == 0:
                ell += period
            need(ell > 0 and ell % 4 == 3, 'positive odd auxiliary index fixture')
            modulus = 4*I*I*f*f
            chi, unused = pell(rho, ell, rho*modulus)
            need(chi % rho == 0, 'odd Chebyshev quotient fixture')
            V = chi//rho
            need((V+c) % (f*f) == 0, 'first interpolated congruence fixture')
            need((V+ell) % (4*I*I) == 0, 'factor4 Chebyshev congruence fixture')
            num = V+c-f*f*(c-R)
            need(num % (4*I*f*f) == 0, 'interpolated T integrality fixture')
            need((num//(4*I*f*f)-residue) % I == 0, 'interpolated T residue fixture')
        fixtures.append({'base': a, 'rank': R, 'strong_index': m,
                         'classes_checked': len(classes), 'strong_I_bits': I.bit_length(),
                         'full_4c2_divisibility': I % (4*c*c) == 0})
    return {'homogeneous_divisibility_assignments': homogeneity,
            'index_valuation_controls': lifting, 'exact_2adic_and_CRT_controls': even,
            'strong_index_binomial_controls': index_multiple,
            'interpolation_modular_fixtures': fixtures,
            'negative_control': 'base2,index2,f7: alpha^8=(1,35) mod49, alpha^56=(1,0) mod49',
            'scope': 'Finite regressions only. No search for a refutation or a polynomial zero.'}


def census(packet):
    nodes = packet['nodes']; names = set(packet['variables']); count = {'add': 0, 'sub': 0, 'mul': 0}
    for k, node in enumerate(nodes):
        tag = node[0]
        if tag in count:
            need(len(node) == 3 and all(type(i) is int and 0 <= i < k for i in node[1:]), 'DAG topology')
            count[tag] += 1
        elif tag == 'variable':
            need(node[1] in names, 'variable leaf')
        elif tag == 'integer':
            need(type(node[1]) is int, 'integer leaf')
        else:
            need(tag == 'coefficient', 'polynomial leaf kind')
    live = set(); pending = [packet['output']]
    while pending:
        k = pending.pop()
        if k not in live:
            live.add(k)
            if nodes[k][0] in count:
                pending.extend(nodes[k][1:])
    need(len(live) == len(nodes), 'entire graph live')
    need({n[1] for n in nodes if n[0] == 'variable'} == names, 'all variables live')
    need({n[1] for n in nodes if n[0] == 'coefficient'} ==
         {'beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B'}, 'all six whole ports live')
    need(count == packet['operation_counts'] and sum(count.values()) == packet['operations'], 'literal operation census')
    return {'variables': len(names), 'degree': packet['exact_degree'],
            'operations': sum(count.values()), 'operation_counts': count, 'all_nodes_live': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scratch', type=Path, default=Path('/tmp/proofs62ff-twelve-interpolation-review'))
    parser.add_argument('--output', type=Path, default=ROOT/'data/twelve-interpolation-review.json')
    args = parser.parse_args(); src = args.scratch/'original/con_zfc_trace_and_interpolation'
    arrival = json.loads((args.scratch/'ARRIVAL.json').read_text())
    archive = ROOT.parent.parent/arrival['archive']
    need(sha(archive) == ARCHIVE_SHA == arrival['sha256'], 'actual archive SHA')
    need(arrival['files'] == 138 and arrival['raw_bytes'] == 4262673, 'complete arrival inventory')
    for entry in arrival['members']:
        path = src.parent/entry['path']
        need(path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'], 'unchanged original member')
    need(len(list(p for p in src.rglob('*') if p.is_file())) == 138, 'no original-tree additions')
    manifest = json.loads((src/'MANIFEST.json').read_text())
    for r in manifest['files']:
        need((src/r['path']).stat().st_size == r['bytes'] and sha(src/r['path']) == r['sha256'], 'release manifest')
    inherited = json.loads((src/'provenance/INHERITED_FILES.json').read_text())
    for r in inherited['files']:
        need((src/r['path']).stat().st_size == r['bytes'] and sha(src/r['path']) == r['sha256'], 'inherited inventory')
    binding = json.loads((src/'inherited/root_fusion/coefficients/BINDING.json').read_text())
    hashes = {}; raw_bytes = 0
    for port, r in binding['payloads'].items():
        raw = gzip.decompress((src/'inherited/root_fusion/coefficients'/r['file']).read_bytes())
        digest = hashlib.sha256(raw).hexdigest()
        need(digest == r['raw_sha256'], 'raw fixed coefficient')
        hashes[port] = digest; raw_bytes += len(raw)
    prior = json.loads((ROOT/'data/saturated-certificates-integer-review.json').read_text())['whole_tuple_raw_hashes']
    need(hashes == prior and raw_bytes == 615883, 'unchanged whole six-source34 tuple')
    normal = json.loads((args.scratch/'normal-receipt.json').read_text())
    opt = json.loads((args.scratch/'optimized-receipt.json').read_text())
    need(normal['status'] == opt['status'] == 'PASS' and not normal['python_optimized'] and opt['python_optimized'], 'two full release replay modes')
    need({k: v for k, v in normal.items() if k != 'python_optimized'} ==
         {k: v for k, v in opt.items() if k != 'python_optimized'}, 'mode-independent release results')
    circuits = {}
    for name in ['monotone_intersective12_degree4832', 'monotone_intersective12_degree16000', 'trace13_degree1072']:
        path = src/'equations'/(name+'.json')
        packet = json.loads(path.read_text())
        circuits[name] = dict(census(packet), sha256=sha(path), serialized_bytes=path.stat().st_size)
    result = {'status': 'PASS ordinary new-reduction review and full finite release replays',
        'scope': 'All three unrestricted-integer equations; inherited ordinary native/refutation calibration remains a named dependency. No Lean or internal-ZFC endpoint claimed.',
        'arrival': {k: arrival[k] for k in ['archive', 'sha256', 'files', 'raw_bytes']},
        'original_unchanged': True, 'manifest_entries': len(manifest['files']),
        'inherited_entries': len(inherited['files']), 'whole_source34_raw_hashes': hashes,
        'raw_coefficient_bytes': raw_bytes, 'focused_mode_optimized': not __debug__,
        'local_exact_checks': local_identities(), 'arithmetic_controls': arithmetic_controls(),
        'literal_circuits': circuits, 'full_release_replays': {'normal': normal, 'optimized': opt},
        'proof_assessment': [
            'S=0 gives the nonzero real-quadratic quintic norm, before guard recovery.',
            'I=s*r*c² and odd nonzero weights establish one-imaginary-root guard recovery on all signed inputs.',
            'R>0 follows from the determinant and authentic MC<beta<MF before product bounds.',
            'Full signed-subset separation handles dependent square classes and a zero guard root.',
            'Normalized strong-rank divisibility replaces the old odd-multiplier use; signed auxiliary step-down needs no multiplier parity.',
            'One strong I,f is fixed before the intersective residue; gcd(4mf,4I²)|4I gives all residues.',
            'Odd-prime rank plus binomial lifting and the exact2-adic formula establish the required valuation bound.',
            'Trace13 recovers v=q²(2s+1) before guard/squarehood without assuming irrational-root independence.'],
        'comparison': 'New12Z4832/248 and16000/223;13Z1072/190 dominates reviewed13Z1088/195. Canonical13-positive90/51 has a different domain and whole compact44 binding.'}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status': 'PASS', 'mode_optimized': not __debug__,
                      'members': 138, 'whole_port_bytes': raw_bytes, 'circuits': circuits}))


if __name__ == '__main__':
    main()
