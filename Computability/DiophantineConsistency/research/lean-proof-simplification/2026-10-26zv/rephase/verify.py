#!/usr/bin/env python3
"""Read-only static/finite checks, never Lean elaboration or archive execution.

Runs with Python 3's standard library from any working directory. Optional
--source-root points to the read-only pinned repository root and checks its
exact target and five relevant source fixtures. This program writes nothing,
launches no subprocess, imports no repository code and performs no networking.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import itertools
import json
import re

ROOT = Path(__file__).resolve().parent
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
NAME = 'CurrentWordRephase2011.lean'
PIN = '9d9d1123b39927d30363f1dcd53c23f0575c30ee'
OLD = """  have hraw : CurrentCarryConstruction2011.raw c W' =
      CurrentCarryConstruction2011.raw c W := by
    funext i
    simp only [CurrentCarryConstruction2011.raw,hr]
  refine ⟨hf.carry_bound,hf.digit_bound,?_,?_,hf.word_bound,?_⟩
  · intro i
    rw [hraw]
    exact hf.recurrence i
  · intro i
    rw [hraw]
    exact hf.decomposition i
"""
NEW = """  refine ⟨hf.carry_bound,hf.digit_bound,?_,?_,hf.word_bound,?_⟩
  · intro i
    simpa only [CurrentCarryConstruction2011.raw,hr] using hf.recurrence i
  · intro i
    simpa only [CurrentCarryConstruction2011.raw,hr] using hf.decomposition i
"""

def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def static_checks(source_root):
    manifest = json.loads((ROOT / 'source_manifest.json').read_text())
    require(manifest['pin'] == PIN, 'pin mismatch')
    for rel, sha in manifest['files'].items():
        require(digest((ROOT / rel).read_bytes()) == sha, 'fixture hash: ' + rel)
    a = (ROOT / 'source' / NAME).read_text()
    b = (ROOT / 'candidate' / NAME).read_text()
    require(a.count(OLD) == 1, 'source exact replacement block')
    require(b == a.replace(OLD, NEW), 'only the declared proof fragment changes')
    require(a[:a.index(OLD)] == b[:b.index(NEW)], 'complete unchanged prefix/signature')
    require(a.split(OLD)[1] == b.split(NEW)[1], 'complete unchanged suffix/transport/clients')
    declarations = re.findall(r'^theorem (\w+)', a, flags=re.M)
    require(declarations == re.findall(r'^theorem (\w+)', b, flags=re.M), 'public names')
    require(len(declarations) == 8, 'eight retained public theorems')
    forbidden = r'\b(sorry|admit|axiom|unsafe|native_decide)\b'
    require(re.search(forbidden, NEW) is None, 'no added proof escape hatch')
    patch = ''.join(difflib.unified_diff(a.splitlines(True), b.splitlines(True),
        fromfile='a/' + str(REL / NAME), tofile='b/' + str(REL / NAME)))
    require(patch == (ROOT / 'patches/rephase-exact-field-rewrite.patch').read_text(),
            'exact full-file unified diff')
    require('CurrentCarryConstruction2011.raw' in (ROOT/'evidence/CurrentCarryConstruction2011.lean').read_text()
            or 'def raw ' in (ROOT/'evidence/CurrentCarryConstruction2011.lean').read_text(), 'raw source fixture')
    if source_root is not None:
        require((source_root / REL / NAME).read_bytes() == (ROOT / 'source' / NAME).read_bytes(),
                'supplied source root target differs from pin fixture')
        for path in sorted((ROOT / 'evidence').glob('*.lean')):
            require(path.read_bytes() == (source_root / REL / path.name).read_bytes(),
                    'supplied source root dependency: ' + path.name)
    return dict(pin=PIN, source_sha256=digest(a.encode()), candidate_sha256=digest(b.encode()),
                old_lines=len(a.splitlines()), new_lines=len(b.splitlines()),
                old_bytes=len(a.encode()), new_bytes=len(b.encode()), net_lines=-6,
                added_helpers=0, added_imports=0, changed_definitions=0,
                public_theorems=declarations, unchanged_transport_and_all_later_clients=True,
                compared_supplied_source_root=source_root is not None)

def word(radix, c):
    return sum(x * radix**i for i, x in enumerate(c))

def rotation(v, W, c):
    n = len(c)
    radix, scale = 2**v, 2**(W % v)
    shifted = tuple((scale*c[i]) % radix + (scale*c[(i-1)%n]) // radix for i in range(n))
    return tuple(shifted[(i-W//v)%n] for i in range(n))

def folded_kernel(radix, n, K):
    out, place = [0]*n, 0
    while K:
        K, digit = divmod(K, radix)
        out[place % n] += digit
        place += 1
    return out

def raw_values(v, W, c, K):
    n = len(c)
    folded = folded_kernel(2**v, n, K)
    rot = rotation(v, W, c)
    return tuple(sum(folded[j]*c[(i-j)%n] for j in range(n)) + rot[i] for i in range(n))

def normalize(radix, raw):
    n, k = len(raw), (0,)*len(raw)
    bound = max(raw)//(radix-1)+2
    for _ in range(n*bound+1):
        nxt = tuple((raw[i]+k[(i-1)%n])//radix for i in range(n))
        if nxt == k:
            d = tuple((raw[i]+k[(i-1)%n])%radix for i in range(n))
            return k, d
        require(all(nxt[i] >= k[i] for i in range(n)), 'monotone finite carry model')
        k = nxt
    raise SystemExit('FAIL: finite carry model did not stabilize')

def finite_checks():
    cases = field_instances = strict_quotients = unequal_quotients = nonboolean = 0
    # Reduced-radix finite instances validate the proof's exact arithmetic
    # pattern. They are not exhaustive for the fixed enormous 2011/47 kernel.
    for n in range(1, 5):
        for v in range(1, 4):
            radix, modulus = 2**v, 2**(v*n)-1
            for c in itertools.product(range(3), repeat=n):
                C = word(radix, c)
                for W in range(2*v*n+1):
                    rot = rotation(v, W, c)
                    require((word(radix, rot) - 2**W*C) % modulus == 0, 'old rotation congruence')
                    for K in (0, 1, 5):
                        raw = raw_values(v, W, c, K)
                        carry, digits = normalize(radix, raw)
                        F = word(radix, digits)
                        require(all(x <= 57 for x in carry), 'finite carry bound')
                        require(all(x < radix for x in digits), 'finite digit bound')
                        require(F <= modulus, 'finite word bound')
                        A = (K+2**W)*C
                        require((A-F) % modulus == 0, 'old scalar congruence')
                        for periods in (1, 2):
                            Wprime = W + periods*v*n
                            require(rotation(v, Wprime, c) == rot, 'actual rotation equality')
                            new_raw = raw_values(v, Wprime, c, K)
                            require(raw == new_raw, 'pointwise raw equality eliminated by simp')
                            for i in range(n):
                                incoming = carry[(i-1)%n]
                                require(carry[i] == (new_raw[i]+incoming)//radix, 'same recurrence')
                                require(new_raw[i]+incoming == digits[i]+radix*carry[i], 'same decomposition')
                                field_instances += 2
                            Aprime = (K+2**Wprime)*C
                            require((Aprime-F)%modulus == 0, 'new scalar congruence, not multiplier equality')
                            if F < modulus:
                                z, zprime = A//modulus+1, Aprime//modulus+1
                                require(z > 0 and zprime > 0, 'positive recomputed quotient')
                                require(A == F+(z-1)*modulus, 'old quotient identity')
                                require(Aprime == F+(zprime-1)*modulus, 'new quotient identity')
                                require(Aprime+(modulus+1-F)-zprime*modulus == 1, 'transport factor one')
                                strict_quotients += 1
                                if C:
                                    require(zprime > z, 'nonzero source genuinely changes quotient')
                                    unequal_quotients += 1
                            cases += 1
                            nonboolean += any(x > 1 for x in c)
    # Explicit negative guards: cyclic shift congruence is essential, whereas
    # equality of the corresponding ordinary multipliers/quotients is false.
    require(rotation(2, 0, (1, 0)) != rotation(2, 2, (1, 0)), 'nonperiod shift negative guard')
    require(rotation(2, 0, (1,)) == rotation(2, 2, (1,)), 'one-cell complete period guard')
    require(2**0 != 2**2, 'ordinary multiplier inequality guard')
    require((1+2**0)//3+1 == 1 and (1+2**2)//3+1 == 2, 'recomputed quotient counterexample')
    return dict(reduced_radix_cases=cases, exact_recurrence_and_decomposition_instances=field_instances,
                strict_quotient_cases=strict_quotients, genuinely_changed_quotients=unequal_quotients,
                nonboolean_source_cases=nonboolean, dimensions='n=1..4, v=1..3',
                source_digits='all maps into {0,1,2}', ordinary_multipliers_identified=False,
                negative_guards=['nonperiod rotation differs', 'same rotation but multipliers differ',
                                 'same C/F/carry but positive quotient changes'],
                concrete_witness=dict(radix=4,n=1,K=1,c=[1],carry=[0],digits=[2],
                                      W=0,Wprime=2,C=1,F=2,w=1,wprime=4,z=1,zprime=2))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path)
    args = parser.parse_args()
    result = dict(status='PASS', static=static_checks(args.source_root), finite=finite_checks(),
                  validation_scope='Static source accounting and finite arithmetic only; Lean UNCOMPILED.',
                  writes_files=False, runs_subprocesses=False, network_access=False)
    print(json.dumps(result, indent=2, ensure_ascii=False))

if __name__ == '__main__':
    main()
