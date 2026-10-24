#!/usr/bin/env python3
"""Exact arithmetic audit of the positive Pell power certificate.

Substitute every definitional gate symbolically and compare all 17 remaining
constraints with an independently written polynomial version of the pinned
PellRepresentation and PowerRepresentation criteria. This is an identity
audit, not a replacement for the Pell-index theorem used by those sources.
"""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path

from build_equation import Builder


def require(test, message):
    if not test:
        raise RuntimeError(message)


class Poly:
    def __init__(self, terms=None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @classmethod
    def constant(cls, c):
        return cls({(): c})

    @classmethod
    def variable(cls, name):
        return cls({(name,): 1})

    def __add__(self, other):
        if isinstance(other, int):
            other = Poly.constant(other)
        out = defaultdict(int, self.terms)
        for m, c in other.terms.items():
            out[m] += c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly.constant(other) if isinstance(other, int) else -other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            other = Poly.constant(other)
        out = defaultdict(int)
        for a, ca in self.terms.items():
            for b, cb in other.terms.items():
                out[tuple(sorted(a + b))] += ca * cb
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        out = Poly.constant(1)
        for _ in range(n):
            out = out * self
        return out


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=here/'POWER_GRAPH_AUDIT.json')
    args = parser.parse_args()
    b = Builder(positive_powers=True)
    n_atom, k_atom = b.new('input.base'), b.new('input.exponent')
    b.power(n_atom, k_atom)
    values = {i: Poly.variable(v['name']) for i, v in enumerate(b.variables) if i not in b.gates}
    residuals = {}
    for row in b.rows:
        out = row['gate']
        result = Poly()
        output_coefficient = 0
        for coefficient, monomial in row['terms']:
            if out is not None and out in monomial:
                require(monomial == [out], 'nonlinear defining output')
                output_coefficient += coefficient
                continue
            term = Poly.constant(coefficient)
            for index in monomial:
                require(index in values, 'nontopological power gate')
                term = term * values[index]
            result = result + term
        if out is not None:
            require(output_coefficient == 1, 'nonmonic gate')
            values[out] = -result
        else:
            require(row['label'] not in residuals, 'duplicate constraint')
            residuals[row['label']] = result

    names = {v['name']: values[i] for i, v in enumerate(b.variables) if i not in b.gates}
    n, k, m = [names[x] for x in ['input.base', 'input.exponent', 'pow0.output']]
    W,A,T,Z,X,Y = [names['pow0.'+x] for x in ['W','A','T','Z','X','Y']]
    U,V,S,R,B = [names['pow0.pell.'+x] for x in ['U','V','S','R','B']]
    def named(s): return names['pow0.'+s]
    def norm(a,x,y): return x*x+y*y-1-a*a*y*y
    def congruence(left,right,modulus,name):
        return left+modulus*named(name+'.qp.1')-right-modulus*named(name+'.qm.1')
    expected = {
        'A_at_least_two': A-named('slack.a2')-2,
        'index_at_most_Y': Y-k-named('slack.yk'),
        'B_at_least_two': B-named('slack.b2')-2,
        'norm1': norm(A,X,Y),
        'norm2': norm(A,U,V),
        'norm3': norm(B,S,R),
        'B_mod_4Y': B-1-4*Y*named('q4'),
        'V_positive_multiple': V-Y*Y*(named('Vquotient_minus1')+1),
        'B_mod_U': congruence(B,A,U,'B_mod_U'),
        'S_mod_U': congruence(S,X,U,'S_mod_U'),
        'R_mod_4Y': congruence(R,k,4*Y,'R_mod_4Y'),
        'power_congruence': congruence(X+Y*n,Y*A+m,T,'power_congruence'),
        'T_definition': 2*A*n-T-n*n-1,
        'output_bound': T-m-named('slack.gap')-1,
        'base_bound': W-n-named('slack.wn'),
        'exponent_bound': W-k-named('slack.wk'),
        'last_norm': norm(W+1,A,W*Z),
    }
    require(set(residuals) == {'pow0.'+x for x in expected}, 'power constraint inventory')
    for name, polynomial in expected.items():
        require(residuals['pow0.'+name].terms == polynomial.terms,
                'power criterion polynomial mismatch: '+name)
    # The rearrangement used to show A>W>=n is itself an exact identity.
    require(expected['last_norm'].terms == (A*A-1-W**3*(W+2)*Z*Z).terms,
            'last norm rearrangement')
    local_certificates = len(names)-3  # two inputs and one output are exposed
    require(local_certificates == 27, 'positive certificate variable count')
    result = {
        'status': 'PASS',
        'exact_polynomial_constraints': len(expected),
        'exact_definitional_gate_substitutions': len(b.gates),
        'positive_certificate_witnesses': local_certificates,
        'positive_inputs_required': ['base', 'exponent'],
        'optimized_python': not __debug__,
        'sha256': {
            'build_equation.py': sha256((here/'build_equation.py').read_bytes()).hexdigest(),
            'audit_power_graph.py': sha256(Path(__file__).read_bytes()).hexdigest(),
        },
        'constraints_checked': list(expected),
        'theorem_sources': [
            'DiophantineConsistency.PellRepresentation.criterion_iff_pell',
            'DiophantineConsistency.PowerRepresentation.criterion_iff_pow'],
        'scope': 'Exact finite polynomial identity audit; the source Pell-index and power theorems supply semantic correctness.'
    }
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
