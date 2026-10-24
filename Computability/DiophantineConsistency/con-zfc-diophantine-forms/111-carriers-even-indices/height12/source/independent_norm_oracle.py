#!/usr/bin/env python3
"""Independent exact 16-fold norm and centered-degree certificate.

Reads literal JSON; imports no candidate builder, circuit or verifier.
The polynomial oracle successively multiplies conjugates using binomial
substitution, independently of the candidate's compact norm formula.
"""
from collections import Counter, defaultdict
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from math import comb
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
PARENT = ROOT / 'candidates/ten-positive-scaled-norm'
COMMIT = '8380e70262337360af048a88ebcd9c17b4c7808d'
ZERO = (0,)*6


def need(ok, message):
    if not ok:
        raise ValueError(message)


class Poly:
    def __init__(self, value):
        if isinstance(value, int):
            value = {ZERO:value}
        self.t = {m:c for m,c in value.items() if c}

    @staticmethod
    def lift(v):
        return v if isinstance(v, Poly) else Poly(v)

    def __add__(self, other):
        out = defaultdict(int, self.t)
        for m,c in self.lift(other).t.items():
            out[m] += c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m:-c for m,c in self.t.items()})

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        out = defaultdict(int)
        for m,c in self.t.items():
            for n,d in self.lift(other).t.items():
                out[tuple(a+b for a,b in zip(m,n))] += c*d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        need(type(n) is int and n >= 0, 'natural polynomial exponent')
        value, base = Poly(1), self
        while n:
            if n & 1:
                value *= base
            n //= 2
            if n:
                base *= base
        return value


def variable(i):
    mon = [0]*6
    mon[i] = 1
    return Poly({tuple(mon):1})


def norm_oracle(x, radicands):
    f = x
    for d in radicands:
        even, odd = Poly(0), Poly(0)
        for mon, coefficient in f.t.items():
            k = mon[0]
            base = Poly({(0,)+mon[1:]:coefficient})
            for j in range(k+1):
                term = comb(k,j)*base*x**(k-j)*d**(j//2)
                if j % 2:
                    odd += term
                else:
                    even += term
        f = even*even - d*odd*odd
    return f


def evaluate(rows, inputs):
    env = dict(inputs)
    def val(x):
        return x if type(x) is int else env[x]
    for name,op,a,b in rows:
        left, right = val(a), val(b)
        env[name] = left+right if op == '+' else left-right if op == '-' else left*right
    return env


def serial(poly):
    return [[list(m),c] for m,c in sorted(poly.t.items())]


def digest(raw):
    return sha256(raw).hexdigest()


def main():
    pins = {}
    for path in sorted(PARENT.iterdir()):
        if not path.is_file():
            continue
        rel = str(path.relative_to(REPO))
        original = subprocess.run(['git','show',COMMIT+':'+rel],cwd=REPO,capture_output=True,check=True).stdout
        need(path.read_bytes() == original, 'complete original source snapshot '+path.name)
        pins[path.name] = digest(original)
    packet = json.loads((PARENT/'p10_positive_degree816.json').read_bytes())
    rows = packet['source']
    need(packet['domain'] == 'strictly positive integers' and len(packet['witnesses']) == 10, 'ten positive witnesses')
    available = set(packet['witnesses']+packet['fixed_numerals'])
    dependencies = {}
    degrees = {v:1 for v in packet['witnesses']} | {v:0 for v in packet['fixed_numerals']}
    for name,op,a,b in rows:
        need(name not in available and op in ('+','-','*'), 'fresh binary arithmetic gate')
        need(all(type(x) is int or x in available for x in (a,b)), 'topological literal DAG')
        available.add(name)
        dependencies[name] = (a,b)
        da,db = (0 if type(x) is int else degrees[x] for x in (a,b))
        degrees[name] = da+db if op == '*' else max(da,db)
    live = set()
    todo = [packet['output']]
    while todo:
        x = todo.pop()
        if type(x) is int or x in live:
            continue
        live.add(x)
        todo.extend(dependencies.get(x,()))
    need(live == available, 'complete liveness')
    counts = Counter(row[1] for row in rows)
    need(len(rows) == packet['operations'] == 124 and dict(counts) == {'*':74,'+':30,'-':20}, 'actual operation census')
    need(degrees['N'] == packet['syntactic_degree'] == 928, 'actual syntactic degree')
    for name, degree in packet['register_degrees'].items():
        need(degrees[name] == degree, 'register degree '+name)
    # This exact source cut is the final 28 binary gates.
    start = next(i for i,row in enumerate(rows) if row[0] == 'ab')
    tail = rows[start:]
    need(len(tail) == 28, 'complete 28-operation norm tail')
    x,a,b,c,d,omega = [variable(i) for i in range(6)]
    actual = evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=c,fd=d))['N']
    expected = norm_oracle(x,[a,b,c,d])
    need(actual.t == expected.t, 'literal 28-gate norm equals independent product of all16 conjugates')
    centered = evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega,fd=d))['N']
    weights = (58,78,84,0,64,102)
    weighted = {mon:sum(i*w for i,w in zip(mon,weights)) for mon in centered.t}
    maximum = max(weighted.values())
    top = {mon:centered.t[mon] for mon,w in weighted.items() if w == maximum}
    need(maximum == 816 and top == {(0,0,0,0,0,8):1}, 'full centered expansion has unique weight816 term omega^8')
    need(all(mon[0] % 2 == 0 for mon in centered.t), 'center appears only through its square')
    bad = deepcopy(tail)
    need(bad[-1][0] == 'N' and bad[-1][1] == '-', 'known corruption target')
    bad[-1][1] = '+'
    need(evaluate(bad,dict(fs=x*x,fa=a,fb=b,fc=c,fd=d))['N'].t != expected.t, 'corrupted norm polarity rejected')
    # No coefficient generator is executed. Use the retained complete tuple.
    coefficient_dir = ROOT/'candidates/split116-compact/compact57/coefficients/compact_tuple'
    ports = {}
    for name,pin in packet['coefficient_binding']['ports'].items():
        blob = (coefficient_dir/pin['file']).read_bytes()
        raw = gzip.decompress(blob)
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'], 'exact fixed coefficient bytes')
        value = int.from_bytes(raw,'little')
        need(value.bit_length() == pin['bits'], 'coefficient bit length')
        ports[name] = dict(raw_sha256=digest(raw),bits=value.bit_length())
        if name == 'beta':
            need(value == 2**590069-1 and value > 0, 'actual nonzero beta licenses exact leading form')
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),commit=COMMIT,
        complete_source_pins=pins,positive_variables=10,operations=124,operation_counts=dict(counts),
        original_norm_terms=len(expected.t),norm_polynomial_sha256=digest(json.dumps(serial(expected),separators=(',',':')).encode()),
        centered_norm_terms=len(centered.t),weighted_degree=maximum,unique_top_term='omega^8',
        centered_polynomial_sha256=digest(json.dumps(serial(centered),separators=(',',':')).encode()),
        corrupted_norm_rejected=True,whole_fixed_tuple=ports,
        exact_degree_scope='Upper816 and unique formal top term checked by complete polynomial expansion. Nonzero actual omega0 is the unbounded leading-form argument in the peer review and PROOF.md; author line tests are supplementary.',
        scope='Independent literal norm/product identity, full centered weighted-degree certificate, topology/liveness/counts and exact source/tuple binding. No author module, coefficient generator or Lean imported.')
    suffix = '-optimized' if sys.flags.optimize else ''
    output = ROOT/('reviews/ten-positive-scaled-norm-peer-algebra'+suffix+'.json')
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',original_norm_terms=len(expected.t),centered_norm_terms=len(centered.t),degree=maximum,unique_top='omega^8',output=str(output)),indent=2))


if __name__ == '__main__':
    main()
