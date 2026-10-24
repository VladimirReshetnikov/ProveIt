#!/usr/bin/env python3
"""Focused ordinary/Python review of valuation-separated twelve-Z equations.

This reads the complete preserved archive but replays only its integer12
component, whose four stages were run separately in normal/-O scratch copies.
It does not import any arrival builder, replay the direct quartics, invoke
Lean, or modify a source file.
"""
import argparse
import gzip
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('valuation_review_ring',
    ROOT/'candidates/positive11-adaptive-shears/independent_ring.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
Ring = MODULE.Ring
ARCHIVE_SHA = '11267f89709f1bb10ba1237d29733727d9c41cebd783041419eb0773e6e7f937'


def need(ok, label):
    if not ok:
        raise ValueError(label)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_controls():
    u, D, H = [Ring.variable(n) for n in ('u', 'D', 'H')]
    Q0 = u*u+D+3*H*H
    C0 = u*(u*u+3*D)-19*H**3
    C1 = 3*u*u+D
    A = Q0*C0+2*u*D*C1
    B = Q0*C1+2*u*C0
    need(A == u**5+10*u**3*D+5*u*D**2+3*H*H*(u**3+3*u*D)
         -19*H**3*(u*u+D)-57*H**5, 'literal even quintic remainder')
    need(B == 5*u**4+10*u*u*D+D*D+3*H*H*(3*u*u+D)-38*H**3*u,
         'literal odd quintic remainder')
    uu, dd, hh = 1+3*u, 1+3*D, 3*H
    BB = 5*uu**4+10*uu*uu*dd+dd*dd+3*hh*hh*(3*uu*uu+dd)-38*hh**3*uu
    need(all(c % 3 == 0 for c in (BB-1).terms.values()), 'B is universally1mod3 on the exact residue class')
    z = Ring.variable('z')
    need((1+3*z)**3-19 == 9*(z+3*z*z+3*z**3-2), 'ramified-prime3 substitution')
    need(4*4+3 == 19 and 8 % 19 != 0, 'prime19 simple quadratic root')
    need((1**3-19) % 2 == 0 and 3 % 2 != 0, 'prime2 simple cubic root')

    patterns = subsets = 0
    for vS in range(5, 12):
        for guard in [None]+list(range(12)):
            values = [-2*vS, 0, 2, 4]+([] if guard is None else [6+guard])
            for bits in range(1, 1 << len(values)):
                chosen = [v for k, v in enumerate(values) if bits & (1 << k)]
                if len(chosen) >= 2:
                    least = min(chosen)
                    need(least % 2 == 0 and chosen.count(least) == 1,
                         'every multi-root subset has a unique even minimum')
                    subsets += 1
            patterns += 1
    # Exhaust the finite residue facts responsible for the valuation pattern.
    residues = 0
    for v, c, s, r, T in itertools.product(range(3), repeat=5):
        q, W, X = 2, 1, 2
        Y = ((2*v+1)*q**3) % 3
        a = ((X+1)*Y) % 3; H = (4*a+3) % 3; Delta = (a*a+H) % 3
        I = (s*r*c*c) % 3
        Dm = (1+Delta*c*c) % 3; Df = (1+Delta*I*I) % 3
        ell = (X*Y*Y) % 3
        for k in range(3):
            need((1+ell*(ell+1)*k*k) % 3 == 1, 'Dt unit for every first-index residue')
        b0 = (X+a*c) % 3; u0 = (H*T-b0) % 3
        need((a, H, Delta, Dm, Df, u0) == (0, 0, 0, 1, 1, 1), 'unconditional front residue class')
        residues += 1
    return {'exact_ring_identities': ['two quadratic remainder coefficients', 'B−1 has all coefficients divisible by3 after residue substitution', 'ramified-prime3 carrier identity'],
        'valuation_order_patterns': patterns, 'all_subset_order_controls': subsets,
        'exhaustive_F3_front_controls': residues,
        'negative_control': 'Weights with equal squared orders permit sqrt1−sqrt1=0; full subset separation is essential.',
        'scope': 'Local exact identities and finite regressions; the universal noncancellation proof is in the review text.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--scratch', type=Path, default=Path('/tmp/proofs62ff-valuation-signed-review'))
    ap.add_argument('--output', type=Path, default=ROOT/'data/valuation-integer12-review.json')
    args = ap.parse_args(); src = args.scratch/'original/ConZFC_Valuation_and_Signed_Certificates'
    arrival = json.loads((args.scratch/'ARRIVAL.json').read_text())
    need(digest(ROOT.parent.parent/arrival['archive']) == ARCHIVE_SHA == arrival['sha256'], 'whole archive pin')
    need(arrival['files'] == 302 and arrival['raw_bytes'] == 9748999, 'complete original arrival')
    for r in arrival['members']:
        path = src.parent/r['path']
        need(path.stat().st_size == r['bytes'] and digest(path) == r['sha256'], 'original member unchanged')
    manifest = json.loads((src/'MANIFEST.json').read_text())
    for r in manifest['files']:
        path = src/r['path']
        need(path.stat().st_size == r['bytes'] and digest(path) == r['sha256'], 'whole manifest entry')
    need(len([p for p in src.rglob('*') if p.is_file()]) == 302, 'no additions to original tree')
    fixed = src/'integer12/inherited/root_fusion/coefficients'
    binding = json.loads((fixed/'BINDING.json').read_text()); hashes = {}; raw_bytes = 0
    for name, r in binding['payloads'].items():
        raw = gzip.decompress((fixed/r['file']).read_bytes())
        h = hashlib.sha256(raw).hexdigest()
        need(h == r['raw_sha256'], 'raw fixed payload')
        hashes[name] = h; raw_bytes += len(raw)
    old = json.loads((ROOT/'data/twelve-interpolation-review.json').read_text())
    need(hashes == old['whole_source34_raw_hashes'] and raw_bytes == 615883, 'whole tuple identical to interpolation parent')
    prior = ROOT/'candidates/interpolation-shared-norms/source'
    inherited_count = 0
    for p in (prior/'inherited/root_fusion').rglob('*'):
        if p.is_file():
            need(p.read_bytes() == (src/'integer12'/p.relative_to(prior)).read_bytes(), 'unchanged inherited root-fusion member')
            inherited_count += 1
    for name in ['INTERPOLATION12.md', 'TRACE13_PROOF.md', 'INDEPENDENT_REVIEW_HILBERT.md', 'INDEPENDENT_TWELVE_AUDIT.md']:
        need((prior/'proofs'/name).read_bytes() == (src/'integer12/proofs'/name).read_bytes(), 'unchanged interpolation arithmetic dependency')
    normal = json.loads((args.scratch/'normal-scoped.json').read_text())
    opt = json.loads((args.scratch/'optimized-scoped.json').read_text())
    need(normal['status'] == opt['status'] == 'PASS' and not normal['optimized'] and opt['optimized'], 'scoped normal/O replay')
    for receipt in [normal, opt]:
        need(len(receipt['stages']) == 4 and receipt['norm']['matched_terms'] == 20349,
             'complete scoped four-stage replay')
        for name, operations, degree in [('prime_separated12_degree2400.json', 215, 2400),
                                          ('prime_separated12_degree2912.json', 209, 2912)]:
            r = receipt['prime']['equations'][name]
            need(r['operations'] == operations and r['upper_degree'] == degree
                 and r['deliberate_corruption_rejected'], 'whole stated metric and negative control')
    circuits = {}
    for name in ['prime_separated12_degree2400', 'prime_separated12_degree2912']:
        path = src/'integer12/equations'/(name+'.json')
        packet = json.loads(path.read_text())
        need(sum(packet['degree_certificate']['monomial'].values()) == packet['exact_degree'], 'attained degree monomial')
        circuits[name] = {k: packet[k] for k in ['variable_count', 'variables', 'domain', 'exact_degree',
                                                'operations', 'operation_counts', 'degree_certificate']}
        circuits[name]['sha256'] = digest(path)
    result = {'status': 'PASS ordinary12-integer reduction review and scoped finite replays',
        'arrival': {k: arrival[k] for k in ['archive', 'sha256', 'commit', 'files', 'raw_bytes']},
        'scope': 'Only integer12; direct1190/1224 and positive98 supplemental components are excluded from mathematical and replay claims.',
        'original_unchanged': True, 'whole_manifest_entries_checked': len(manifest['files']),
        'whole_source34_raw_hashes': hashes, 'raw_coefficient_bytes': raw_bytes,
        'unchanged_root_fusion_members': inherited_count, 'unchanged_interpolation_proof_files': 4,
        'focused_python_optimized': not __debug__, 'exact_local_checks': exact_controls(),
        'literal_circuits': circuits, 'full_scoped_replays': {'normal': normal, 'optimized': opt},
        'proof_review': ['S=0 is excluded by the real-quadratic root obstruction, before guard recovery.',
            'B≡1mod3 and3|H give the five squared-root valuation orders−2v3S,0,2,4,≥6.',
            'Every changed-sign subset has a unique even minimum even if the guard valuation is odd or negative radicand; zero guard is omitted.',
            'The rational auxiliary root is made integral by a separate adjacent-coefficient descent with Q>1.',
            'Both rational and integral companions recover the same integer main congruence and generalized signed native kernel.',
            'The inherited fixed-I-before-residue interpolation theorem applies unchanged to the new intersective quintic.',
            'Exceptional carrier primes2,3,19 are explicitly lifted, rather than assuming simple cubic roots there.'],
        'comparison': '12Z215/2400 and209/2912 dominate reviewed12Z239/4832 and215/16000;13Z184/1072 retains a lower-degree/cost tradeoff with one additional variable.',
        'formal_boundary': 'Ordinary unbounded proof composed with retained calibration; no new Lean/internal-ZFC assertion.'}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status': 'PASS', 'python_optimized': not __debug__, 'whole_manifest': len(manifest['files']),
                      'scoped_stages_each_mode': 4, 'inherited': inherited_count, 'raw_port_bytes': raw_bytes}))


if __name__ == '__main__':
    main()
