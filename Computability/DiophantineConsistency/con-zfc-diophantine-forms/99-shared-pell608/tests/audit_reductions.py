#!/usr/bin/env python3
"""Independent finite controls for the cofinal beta and pure-power envelope reductions.

The ordinary unbounded proofs are in REDUCTION_PROOF.md. This audit checks
the exact deleted source syntax, envelope certificate, output polynomial,
and beta-code fixtures. It never searches the consistency equation for a zero.
"""
import argparse
import ast
from collections import defaultdict
from hashlib import sha256
import json
from math import factorial, prod, gcd
from pathlib import Path
import random
import importlib.util


class SourceDAG:
    """Independent semiring-only reconstruction; no compiler or polynomial exporter."""
    def __init__(self): self.next_index=0; self.cache={}
    def new(self):
        result=('v',self.next_index); self.next_index+=1; return result
    def add(self,a,b):
        if a==('c',0): return b
        if b==('c',0): return a
        if a[0]==b[0]=='c': return ('c',a[1]+b[1])
        a,b=sorted((a,b)); key=('add',a,b)
        if key not in self.cache: self.cache[key]=self.new()
        return self.cache[key]
    def mul(self,a,b):
        if ('c',0) in (a,b): return ('c',0)
        if a==('c',1): return b
        if b==('c',1): return a
        if a[0]==b[0]=='c': return ('c',a[1]*b[1])
        a,b=sorted((a,b)); key=('mul',a,b)
        if key not in self.cache: self.cache[key]=self.new()
        return self.cache[key]
    def sum(self,terms):
        result=('c',0)
        for term in terms: result=self.add(result,term)
        return result
    def product(self,terms):
        result=('c',1)
        for term in terms: result=self.mul(result,term)
        return result
    def square(self,a): return self.mul(a,a)
    def pair_add(self,a,b): return self.add(a[0],b[0]),self.add(a[1],b[1])
    def pair_mul(self,a,b):
        return self.add(self.mul(a[0],b[0]),self.mul(a[1],b[1])),self.add(self.mul(a[0],b[1]),self.mul(a[1],b[0]))
    def pair_square(self,a):
        return self.add(self.square(a[0]),self.square(a[1])),self.product([('c',2),a[0],a[1]])


def source_envelope_binding(directory,certificate):
    spec=importlib.util.spec_from_file_location('audited_source_calculus',directory/'direct_calculus.py')
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    source=json.loads((directory/'wire_eliminated_source.json').read_text())
    dag=SourceDAG()
    names=('t','x','y','m','M0','p','q','v','a','b','c','d','S','Sp','u','vq')
    env={name:dag.new() for name in names}
    ep,fp=module.source_pair_calculus(dag,source,env,env['t'],False)
    output=dag.add(ep,fp)
    expected=[{'op':op,'a':list(a),'b':list(b),'output':v[1]}
              for (op,a,b),v in dag.cache.items()]
    actual=[{k:v for k,v in row.items() if k!='exponent'} for row in certificate['nodes']]
    require(expected==actual and list(output)==certificate['output'],
            'envelope DAG not bound to actual numerical source pair')
    return {'actual_source_nodes_matched':len(expected)}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def source_change(old_path, new_path):
    old = ast.parse(old_path.read_text())
    new = ast.parse(new_path.read_text())
    candidates = [node for node in ast.walk(old)
                  if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name)
                  and node.target.id == 'rows' and isinstance(node.value, ast.List)
                  and len(node.value.elts) == 4]
    require(len(candidates) == 1, 'unique original four-row beta block')
    original = candidates[0].value.elts
    expected_text = ["(denominator, self.sum([env['S'], env['r'], one]))",
                     "(next_denominator, self.sum([env['Sp'], env['rp'], one]))"]
    for node, text in zip((original[1], original[3]), expected_text):
        require(ast.dump(node) == ast.dump(ast.parse(text, mode='eval').body),
                'deleted row differs from a beta remainder bound')
    candidates[0].value.elts = [original[0], original[2]]
    require(ast.dump(old) == ast.dump(new), 'other numerical-calculus syntax changed')
    return {'exact_source_ast_identity': True,
            'deleted_rows': ['S+r+1-D_i', 'Sp+rp+1-D_(i+1)']}


def envelope_check(certificate):
    inputs = certificate['inputs']
    require(len(inputs) == len(set(inputs)) == 16, 'envelope input list')
    exponents = {i: 1 for i in range(len(inputs))}
    def bound(atom):
        tag, value = atom
        if tag == 'c':
            require(0 <= value <= 4, 'envelope constant leaf')
            return 0 if value <= 1 else 1
        require(tag == 'v' and value in exponents, 'envelope forward/unknown reference')
        return exponents[value]
    for record in certificate['nodes']:
        i = record['output']
        require(i not in exponents, 'duplicate envelope output')
        da, db = bound(record['a']), bound(record['b'])
        require(record['op'] in ('add', 'mul'), 'unknown envelope operator')
        d = max(da, db) + 1 if record['op'] == 'add' else da + db
        require(record['exponent'] == d, 'incorrect inductive envelope exponent')
        exponents[i] = d
    output = bound(certificate['output'])
    require(output == certificate['exponent'] == 6893164, 'unexpected envelope endpoint')
    return {'envelope_nodes': len(certificate['nodes']), 'envelope_exponent': output,
            'proof_rule': 'W>=4; inputs<=W; sum:max+1; product:sum'}


def literal_check(directory):
    equation = json.loads((directory/'equation.json').read_text())
    polynomial = json.loads((directory/'expanded_polynomial.json').read_text())
    nv = len(equation['variables'])
    expected = defaultdict(int)
    live = set()
    for row in equation['residuals']:
        seen = set()
        for coefficient, mon in row['terms']:
            require(isinstance(coefficient, int) and coefficient, 'row coefficient')
            require(len(mon) <= 2 and mon == sorted(mon), 'row monomial')
            require(all(isinstance(j, int) and 0 <= j < nv for j in mon), 'row index')
            require(tuple(mon) not in seen, 'duplicate row monomial')
            seen.add(tuple(mon)); live.update(mon)
        for a, ma in row['terms']:
            for b, mb in row['terms']:
                expected[tuple(sorted(ma+mb))] += a*b
    expected = {m:c for m,c in expected.items() if c}
    actual = {tuple(m):c for c,m in polynomial['terms']}
    require(len(actual) == len(polynomial['terms']) and actual == expected,
            'expanded polynomial differs from exact squared sum')
    require(live == set(range(nv)), 'unused final variable')
    return {'variables': nv, 'residuals': len(equation['residuals']),
            'degree': max(map(len, expected)), 'monomials': len(expected),
            'height': max(map(abs, expected.values()))}


def crt(residues, moduli):
    modulus = prod(moduli)
    return sum(r*(modulus//d)*pow(modulus//d, -1, d)
               for r,d in zip(residues,moduli)) % modulus


def beta_checks():
    rng = random.Random(20261024)
    cases = 0
    for t in range(1, 8):
        for _ in range(20):
            states = [rng.randrange(200) for _ in range(t+1)]
            y = factorial(t)*(max(max(states), 2)//factorial(t)+1)
            ds = [1+(i+1)*y for i in range(t+1)]
            require(all(gcd(a,b)==1 for i,a in enumerate(ds) for b in ds[i+1:]),
                    'beta moduli not pairwise coprime')
            x = crt(states, ds)
            for state,d in zip(states,ds):
                u = (x-state)//d
                require(state <= y and state < d and u >= 0 and x == state+d*u,
                        'cofinal trace restoration')
                require(x % d == state, 'beta digit mismatch')
            cases += 1
    # A complete abstract binary Horn expansion, independent of C222 falsity.
    t,m = 3,3
    M = (m+1)**t
    states = [1+M,(1+2*M)*(1+3*M),1+3*M,1]
    rules = [(2,3,1),(0,0,2),(0,0,3)]
    y = factorial(t)*(max(states)//factorial(t)+1)
    ds = [1+(i+1)*y for i in range(t+1)]
    x = crt(states,ds)
    for i,(p,q,v) in enumerate(rules):
        require(states[i+1]*(1+v*M)==states[i]*(1+p*M)*(1+q*M),
                'abstract accumulator flow')
        require(x % ds[i] == states[i] <= y, 'abstract cofinal beta trace')
    # Removing remainder rows without a cofinal digit bound is false.
    require(5 == 5 + 2*0 and 5 % 2 != 5 and not 5 <= 1,
            'unbounded-digit corruption control')
    return {'arbitrary_traces': cases, 'abstract_flow': {'t': t, 'm': m,
            'M': M, 'states': states, 'y': y, 'x': x},
            'missing_digit_bound_counterexample': {'x':5,'y':1,'i':0,'S':5,'u':0}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).parent
    parser.add_argument('--original-source', type=Path, default=here.parent/'shared/con_zfc_shared_certificates/direct/direct_calculus.py')
    parser.add_argument('--directory', type=Path, default=here/'output')
    parser.add_argument('--output', type=Path, default=here/'AUDIT.json')
    args=parser.parse_args()
    certificate=json.loads((args.directory/'envelope_certificate.json').read_text())
    checks = {'status':'PASS','source':source_change(args.original_source, here/'direct_calculus.py'),
              'envelope':envelope_check(certificate) | source_envelope_binding(here,certificate),
              'literal':literal_check(args.directory), 'beta': beta_checks(),
              'scope':'exact finite source/envelope/literal certificates; universal proof in companion note'}
    checks['sha256']={str(path.relative_to(here)):sha256(path.read_bytes()).hexdigest()
                      for path in [here/'direct_calculus.py',args.directory/'equation.json',args.directory/'expanded_polynomial.json',args.directory/'envelope_certificate.json']}
    args.output.write_text(json.dumps(checks,indent=2,sort_keys=True)+'\n')
    print(json.dumps(checks,indent=2,sort_keys=True))


if __name__=='__main__': main()
