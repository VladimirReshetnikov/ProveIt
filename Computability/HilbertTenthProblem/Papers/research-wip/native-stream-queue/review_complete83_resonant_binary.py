#!/usr/bin/env python3
"""Fresh independent binary-population controls; frozen dependencies are inert."""
from pathlib import Path
import argparse, hashlib, json

PINS = {'complete83_plus_resonant_population.md': 'c09e8a550a66cd89fe8b4281000d84c3bd5db2fe390d07c28e33348c7d93b31a', 'complete83_plus_resonant_population.py': 'bd93b5773847eb1a48e32c63d37ef45d8be4a3c4ad78ed5fbe15c6b1e2fea3e0', 'complete83_plus_resonant_population.json': '04bdee149b217bc12dd2b1e0e924412cc9dc61e4658b4c73244d83f260dd437d', 'complete83_resonant_minus_binary.md': '5d130699b2060dcd0d5eee1f4ecd312a9a098bf36adb868c29b7e0491f445ed1', 'complete83_resonant_minus_binary.py': 'f327e4bad18f8ab9ca9065a41ef0814a958fb1302a6e1c0d9124c5e7a88b5e25', 'complete83_resonant_minus_binary.json': 'a7e0c91ad1e51e1eb5e517fb2ff6328ce69b5ed1e839caadc9083d05ad563cf4', 'complete83_growing_resonant_selectors.md': 'c005748a280f385c0278e6bfbf4c9f465e924ef9687ad773031d97d3a5760e15', 'complete83_growing_resonant_selectors.py': '62f3a6750357f593f809f74fad63fae4fb7b716dc28a36333a32898f7b802d57', 'complete83_growing_resonant_selectors.json': '141d51917d28d4ead733e722f0e466383d780ca130cb09222273d7f531e36718'}

def check(ok, why):
    if not ok:
        raise ValueError(why)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def mersenne_controls():
    count = 0
    for d in range(3, 34):
        B = 1 << d
        m = B-1
        for multiplier in range(1, 258):
            value = m*multiplier
            check(value.bit_count() >= d, 'positive Mersenne multiple')
            count += 1
        for j in range(1, 129):
            value = (j*j+1)*(B*B+3*B+7)
            x = value
            while x >= B:
                low, high = x % B, x // B
                y = low+high
                check(y < x and y.bit_count() <= x.bit_count(), 'fold monotonicity')
                x = y
            remainder = 0 if x == m else x
            check(remainder == value % m, 'fold residue')
            check(remainder.bit_count() <= value.bit_count(), 'cyclic population')
            count += 1
    return {'cases': count, 'scope': 'Finite independent Mersenne folding and positive-multiple controls.'}

def population_controls():
    records = []
    for d in (25, 45, 125):
        B = 1 << d
        m = B-1
        mask_defect = 1+(1 << (d//3))
        native_MF = 4+(1 << (d//2))
        MC = m-mask_defect
        MF = m+native_MF
        K = (1 << (d+3))+(1 << (d+5))
        e = mask_defect.bit_count()
        check(MC % 4 == 2 and native_MF.bit_count() == e, 'relaxed mask conditions')
        check(d > 2*K.bit_count()*e+2*e, 'minus sufficient scalar margin')
        for n in (17, 33, 65):
            D = d*n
            Q = 1 << D
            repeat = (Q-1)//m
            for hbase in (4*n*n, 4*n*n+68, 4*n*n*n):
                for shape in ('plus', 'minus'):
                    h = hbase if shape == 'plus' else hbase+1
                    A = Q+1 if shape == 'plus' else 2*Q-1
                    q = Q*(Q+1)//2 if shape == 'plus' else Q*(2*Q-1)
                    za = 1+(m-MC//2)*repeat if shape == 'plus' else 2*mask_defect*repeat
                    z = za+A*h
                    F = K*z
                    J = (q-1)//m
                    check(m*J == q-1, 'repunit integrality')
                    R = q**4-F*q**3-(z+1)*q*q+F*q+z+(MC+q*MF)*J
                    check(R > 0 and R % 4 == 3 and (R+1) % A == 0, 'resonant index conditions')
                    t = D-1 if shape == 'plus' else D
                    pc = R.bit_count()
                    check(pc >= 3*t+2, 'finite binary threshold')
                    if shape == 'plus':
                        H = m-MC//2
                        c, v = divmod(K*H, m)
                        check(H.bit_count() == e, 'plus sparse residue word')
                        check(F == (c+K*h)*Q+v*repeat+K-c+K*h, 'plus two-limb identity')
                        low = (MC//2)*repeat+h+Q//2
                        check(R % Q == low % Q, 'plus low residue')
                        check(2*d-2*e-5*v.bit_count() > 0, 'plus fixed density margin')
                        scaled = 16*R
                        digits = [(scaled >> (i*D)) & (Q-1) for i in range(9)]
                        check(digits[8] == 0, 'plus top borrow')
                        high_population = sum(x.bit_count() for x in digits[4:8])
                        check(high_population+(R % Q).bit_count() <= pc, 'disjoint plus windows')
                    else:
                        v = (2*K*mask_defect) % m
                        residues = [mask_defect, -(v+2*mask_defect+native_MF),
                                    2*v-2*mask_defect, v+8*mask_defect+4*native_MF,
                                    -(6*v+8*mask_defect), 12*v, -8*v]
                        weights = [(c % m).bit_count() for c in residues]
                        check(v and (v+2*mask_defect+native_MF) % m and (6*v+8*mask_defect) % m,
                              'minus nonzero complement residues')
                        check(sum(weights)+d >= 4*d-2*v.bit_count()-2*e > 3*d,
                              'minus limiting rate')
                        check(R % Q == (mask_defect*repeat-h-1) % Q, 'minus low residue')
                    records.append({'d': d, 'n': n, 'shape': shape, 'h': h,
                                    'R_bits': R.bit_length(), 'R_population': pc,
                                    'required_population': 3*t+2})
    return {'cases': len(records), 'records_sha256': sha(json.dumps(records, sort_keys=True).encode()),
            'minimum_population_margin': min(x['R_population']-x['required_population'] for x in records),
            'maximum_R_bits': max(x['R_bits'] for x in records),
            'scope': 'Relaxed synthetic fixed masks and coefficients; neither compiler outputs nor shifted CRT depth choices. No X=2^R, half-binomial, Pell tuple or full source zero is evaluated.'}

def make(root):
    bindings = {}
    for name, expected in PINS.items():
        raw = (root/name).read_bytes()
        check(sha(raw) == expected, 'dependency mismatch '+name)
        bindings[name] = {'bytes': len(raw), 'sha256': expected}
    return {'status': 'PASS: independent finite controls only; all-size review in separate prose',
            'reviewer_source_sha256': sha(Path(__file__).read_bytes()),
            'bindings': bindings, 'mersenne_controls': mersenne_controls(),
            'population_controls': population_controls(),
            'scope': {'predecessor_or_author_code_executed': False, 'actual_compiler_evaluated': False,
                      'complete_positive_zero_evaluated': False}}

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--root', required=True, type=Path)
    p.add_argument('--write', type=Path)
    p.add_argument('--expect', type=Path)
    a = p.parse_args()
    result = make(a.root)
    raw = (json.dumps(result, indent=2, sort_keys=True)+'\n').encode()
    if a.write:
        a.write.write_bytes(raw)
    if a.expect:
        check(a.expect.read_bytes() == raw, 'exact receipt mismatch')
    print(json.dumps({'status': 'PASS', 'population_cases': result['population_controls']['cases'],
                      'receipt_sha256': sha(raw)}))

if __name__ == '__main__':
    main()
