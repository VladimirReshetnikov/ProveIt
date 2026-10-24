#!/usr/bin/env python3
"""Independent exact checks for the ten-positive-variable polynomial.

This program imports neither the builder nor its algebra routines.  It
multiplies the sixteen linear radical factors in a sparse integer polynomial
ring, checks every named circuit cut, audits the literal graph, proves its
degree by a unique leading norm monomial, and compares all named registers
modulo several moduli using the authentic coefficient bytes.

The modular comparisons and bounded controls are diagnostics.  The norm
identity, local circuit identities, and degree certificate are exact.  None
of these finite checks replaces the unbounded semantic proof in PROOF.md.
"""
from collections import Counter
from copy import deepcopy
from itertools import product
from pathlib import Path
import gzip
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parent


class Poly:
    """Sparse Z-polynomial; a monomial is a sorted tuple of variable names."""
    def __init__(self, terms=None):
        if isinstance(terms, int):
            terms = {(): terms} if terms else {}
        self.t = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def var(name):
        return Poly({(name,): 1})

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Poly) else Poly(x)

    def __add__(self, other):
        other = self.coerce(other)
        out = self.t.copy()
        for m, c in other.t.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.t.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        out = {}
        for m, c in self.t.items():
            for n, d in other.t.items():
                mn = tuple(sorted(m + n))
                out[mn] = out.get(mn, 0) + c * d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError('Only nonnegative integer powers are allowed')
        out, base = Poly(1), self
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def __eq__(self, other):
        return self.t == self.coerce(other).t

    def substitute(self, replacements):
        out = Poly()
        for monomial, coefficient in self.t.items():
            term = Poly(coefficient)
            for name in monomial:
                term *= replacements.get(name, Poly.var(name))
            out += term
        return out


def require(condition, message):
    if not condition:
        raise ValueError(message)


def norm_from_linear_factors():
    z = Poly.var('Z')
    roots = [Poly.var('r' + str(i)) for i in range(4)]
    answer = Poly(1)
    for signs in product((-1, 1), repeat=4):
        answer *= z - sum(s * r for s, r in zip(signs, roots))
    # Set r0^2=A, r1^2=B, r2^2=D, r3^2=C/delta and multiply by delta^8.
    converted = {}
    for monomial, coefficient in answer.t.items():
        powers = Counter(monomial)
        require(all(powers['r' + str(i)] % 2 == 0 for i in range(4)),
                'A radical survived the complete conjugate product')
        c_power = powers['r3'] // 2
        require(c_power <= 8, 'Unexpected denominator degree')
        target = tuple(sorted(
            ('Z',) * powers['Z'] +
            ('A',) * (powers['r0'] // 2) +
            ('B',) * (powers['r1'] // 2) +
            ('D',) * (powers['r2'] // 2) +
            ('C',) * c_power +
            ('delta',) * (8 - c_power)))
        converted[target] = converted.get(target, 0) + coefficient
    return Poly(converted), len(answer.t)


def compact_norm():
    z, a, b, d, c, h = map(Poly.var, ['Z', 'A', 'B', 'D', 'C', 'delta'])
    sigma = a + b + d
    pairs = a*b + a*d + b*d
    prod3 = a*b*d
    aa = h*(z*z-sigma)+c
    tt = h*c*z*z
    kk = aa*aa+4*(tt-h*h*pairs)
    rr = 16*h*h*h*prod3
    bb = aa*kk-rr
    ee = kk*kk+16*tt*aa*aa-4*rr*(h*z*z+c)
    return ee*ee-64*tt*bb*bb


def expected_named_cuts():
    """Independently typeset equations, using all other named values as cuts."""
    v = Poly.var
    names = ['j','F','alpha','i','T','X','s','n','eta','zeta',
             'beta','K0','MC','MF','J','q_minus_1','q','q2','q3','q4',
             'U','C','Y','E','k','kY','c','c2','a','H','Delta','ell','R',
             'Rhat','Bt','I','I2','Df_minus_1','Df','Q','delta','cT','V',
             'Dt','Dd','Vbar','Gbar','L','W','v','b0','M','center','Z',
             'M2','M2H2','A','B','D','Cnum','sigma','AB','pairs','prod',
             'Z2','delta2','delta3','delta_Z2','ahat','ahat2','tz','khat',
             'rhat','bhat','ehat','P10']
    x = {name:v(name) for name in names}
    # Keeping these local names separate from builder code makes each
    # claimed arithmetic register an independently checked polynomial cut.
    p = {}
    p['J'] = 3*x['j']+1
    p['q_minus_1'] = x['beta']*x['J']
    p['q'] = x['q_minus_1']+1
    p['q2'] = x['q']**2
    p['q3'] = x['q2']*x['q']
    p['q4'] = x['q2']**2
    p['U'] = x['q4']*x['q']
    p['C'] = x['q']-x['F']-x['alpha']
    p['Y'] = x['q3']*x['s']
    p['E'] = x['X']*x['Y']
    p['k'] = x['eta']+x['zeta']
    p['kY'] = x['k']*x['Y']
    p['c'] = x['kY']+x['eta']
    p['c2'] = x['c']**2
    p['a'] = x['E']+x['Y']
    p['H'] = 4*x['a']+3
    p['Delta'] = x['a']**2+x['H']
    p['ell'] = x['E']*x['kY']
    p['R'] = ((x['q_minus_1']*(x['q']-x['F'])+x['alpha'])*
              (x['q2']-1)+(x['MC']+x['q']*x['MF'])*x['J'])
    p['Rhat'] = x['q3']*(x['q']+x['F']+x['alpha'])
    p['Bt'] = (x['q']*x['K0']+x['X'])*x['C']-x['q']*x['F']
    p['I'] = x['i']*x['c2']
    p['I2'] = x['I']**2
    p['Df_minus_1'] = x['Delta']*x['I2']
    p['Df'] = x['Df_minus_1']+1
    p['Q'] = x['Delta']*x['Df_minus_1']
    p['delta'] = x['Q']-1
    p['cT'] = x['c']*x['T']
    p['V'] = x['Df']*(x['cT']-x['R'])-x['c']
    p['Dt'] = x['ell']*(x['ell']+x['k'])+1
    p['Dd'] = x['Delta']*x['c2']+1
    p['Vbar'] = x['Df']*(x['cT']+x['Rhat'])
    p['Gbar'] = 2*x['c']+2*x['X']+x['k']+x['Rhat']+1
    p['L'] = 3*x['Vbar']+x['Gbar']
    p['W'] = x['q_minus_1']*x['L']+1
    p['v'] = x['k']-x['R']-1
    p['b0'] = x['X']+x['a']*x['c']
    p['M'] = x['q_minus_1']*x['U']
    p['center'] = x['ell']+x['k']+x['n']+x['L']+x['s']
    p['Z'] = (x['M']*(x['H']*x['center']+x['b0'])-
              x['H']*x['U']*x['W']*x['Bt']+
              x['H']*x['q_minus_1']*(x['q4']*x['X']-x['v']))
    p['M2'] = x['M']**2
    p['M2H2'] = x['M2']*x['H']**2
    p['A'] = x['M2H2']*x['Dt']
    p['B'] = x['M2H2']*x['Df']
    p['D'] = x['M2']*x['Dd']
    p['Cnum'] = x['M2H2']*(x['Q']*x['V']**2-1)
    p['sigma'] = x['A']+x['B']+x['D']
    p['AB'] = x['A']*x['B']
    p['pairs'] = x['AB']+(x['A']+x['B'])*x['D']
    p['prod'] = x['AB']*x['D']
    p['Z2'] = x['Z']**2
    p['delta2'] = x['delta']**2
    p['delta3'] = x['delta2']*x['delta']
    p['delta_Z2'] = x['delta']*x['Z2']
    p['ahat'] = x['delta']*(x['Z2']-x['sigma'])+x['Cnum']
    p['ahat2'] = x['ahat']**2
    p['tz'] = x['delta']*x['Cnum']*x['Z2']
    p['khat'] = x['ahat2']+4*(x['tz']-x['delta2']*x['pairs'])
    p['rhat'] = 16*x['delta3']*x['prod']
    p['bhat'] = x['ahat']*x['khat']-x['rhat']
    p['ehat'] = (x['khat']**2+16*x['tz']*x['ahat2']-
                 4*x['rhat']*(x['delta_Z2']+x['Cnum']))
    p['P10'] = x['ehat']**2-64*x['tz']*x['bhat']**2
    return p


def operate(op, a, b):
    if op == '+': return a+b
    if op == '-': return a-b
    if op == '*': return a*b
    raise ValueError('Unknown operation: '+repr(op))


def audit_graph(packet):
    variables = packet['variables']
    fixed = packet['fixed_numerals']
    require(len(variables) == len(set(variables)) == 10, 'Variable count')
    require(variables == ['j','F','alpha','i','T','X','s','n','eta','zeta'],
            'Variable convention changed')
    available = set(variables+fixed)
    rows = packet['source']
    depth = {v:0 for v in available}
    degree = {v:(1 if v in variables else 0) for v in available}
    for name, op, a, b in rows:
        require(name not in available, 'Duplicate gate name')
        require(op in ('+','-','*'), 'Uncharged operation')
        require(all(isinstance(x, int) or x in available for x in (a,b)),
                'Forward reference or undefined input')
        da, db = [0 if isinstance(x,int) else degree[x] for x in (a,b)]
        degree[name] = da+db if op == '*' else max(da,db)
        depth[name] = 1+max(0 if isinstance(x,int) else depth[x] for x in (a,b))
        available.add(name)
    output = packet['output']
    require(output in available, 'Undefined output')
    needed = {output}
    for name, op, a, b in reversed(rows):
        if name in needed:
            needed.update((a,b))
    require(all(row[0] in needed for row in rows), 'Dead gate was charged')
    require(set(variables+fixed) <= needed, 'Unused declared input')
    for name, wire in packet['named_registers'].items():
        require(wire in available, 'Undefined named register '+name)
    count = Counter(row[1] for row in rows)
    require(len(rows) == 131, 'Operation count differs from the release')
    require(dict(count) == {'*':77, '+':37, '-':17}, 'Operation breakdown differs')
    require(packet['operations'] == len(rows), 'Stored operation count is wrong')
    require(packet['operation_breakdown'] == dict(count), 'Stored breakdown is wrong')
    return {'operations':len(rows), 'operation_breakdown':dict(count),
            'depth':depth[output], 'upper_total_degree':degree[output],
            'named_degrees':{k:degree[v] for k,v in packet['named_registers'].items()}}


def polynomial_above_cuts(packet, target, cuts):
    rows = {row[0]:row[1:] for row in packet['source']}
    cache = {}
    def walk(ref):
        if isinstance(ref,int): return Poly(ref)
        if ref in cuts: return Poly.var(cuts[ref])
        if ref in cache: return cache[ref]
        if ref not in rows: return Poly.var(ref)
        op,a,b = rows[ref]
        cache[ref] = operate(op,walk(a),walk(b))
        return cache[ref]
    return walk(target)


def check_all_cuts(packet):
    named = packet['named_registers']
    require(len(named.values()) == len(set(named.values())),
            'Register aliases require explicit review of cut names')
    bywire = {wire:name for name,wire in named.items()}
    expected = expected_named_cuts()
    require(set(expected) == set(named), 'Missing independently typeset register')
    for name, wire in named.items():
        cuts = {w:n for w,n in bywire.items() if w != wire}
        observed = polynomial_above_cuts(packet,wire,cuts)
        require(observed == expected[name], 'Literal cut differs: '+name)
    return len(named)


def check_literal_norm(packet, reference):
    cuts = {packet['named_registers'][name]: ('C' if name=='Cnum' else name)
            for name in ('Z','A','B','D','Cnum','delta')}
    observed = polynomial_above_cuts(packet,packet['output'],cuts)
    require(observed == reference, 'Literal norm differs from conjugate product')


def check_degree(packet, reference, graph):
    deg = graph['named_degrees']
    weights = {name:deg['Cnum' if name=='C' else name]
               for name in ('Z','A','B','D','C','delta')}
    term_degrees = {m:sum(weights[x] for x in m) for m in reference.t}
    maximum = max(term_degrees.values())
    leaders = [(m,reference.t[m]) for m,d in term_degrees.items() if d==maximum]
    wanted = tuple(sorted(('delta',)*8+('Z',)*16))
    require(leaders == [(wanted,1)], 'Leading norm monomial is not unique')
    require(maximum == graph['upper_total_degree'] == 1152, 'Degree disagreement')
    require(packet['exact_total_degree'] == 1152, 'Stored exact degree is wrong')
    # Independently establish the leading-register factorization. q0 is a
    # homogeneous degree-one indeterminate, later replaced by 3*beta*j.
    q,k,x,s,i,t,F,alpha,K = map(Poly.var,
                              ['q0','k0','X','s','i','T','F','alpha','K0'])
    y0 = q**3*s
    a0 = x*y0
    c0 = k*y0
    I0 = i*c0**2
    Df0 = a0**2*I0**2
    Q0 = a0**4*I0**2
    Bt0 = (K*q+x)*(q-F-alpha)-q*F
    Z0 = -4*a0*q**5*(q*(3*Df0*c0*t))*Bt0
    require(Q0 == i**2*k**4*x**4*q**24*s**8, 'Q leader mismatch')
    require(Z0 == -12*i**2*k**5*x**3*q**30*s**8*t*Bt0,
            'Z leader mismatch')
    # At minimum q0 degree the only Bt term with no F is -X*alpha.
    require(Bt0.substitute({'q0':Poly(0),'F':Poly(0)}) == -x*alpha,
            'Selected nonzero coefficient is not isolated')
    # Exponents of Q0^8 Z0^16, before the selected Bt0^16 term.
    core = {'i':2*8+2*16,'k0':4*8+5*16,'X':4*8+3*16,
            'q0':24*8+30*16,'s':8*8+8*16,'T':16}
    selected = {'j':core['q0'],'i':core['i'],'eta':core['k0'],
                'X':core['X']+16,'s':core['s'],'T':core['T'],'alpha':16}
    require(sum(selected.values()) == maximum, 'Leading witness total degree')
    return {'exact_degree':maximum, 'norm_cut_weights':weights,
            'unique_norm_leading_term':'delta^8 * Z^16',
            'witness_monomial':selected,
            'witness_coefficient':'12^16 * (3*beta)^672 > 0',
            'reason':'Minimum j degree forces Bt0=-X*alpha after F=0; '
                     'eta^112 has coefficient one in (eta+zeta)^112.'}


def literal_values(packet,inputs,modulus):
    values = {k:v % modulus for k,v in inputs.items()}
    def get(ref): return ref % modulus if isinstance(ref,int) else values[ref]
    for name,op,a,b in packet['source']:
        values[name] = operate(op,get(a),get(b)) % modulus
    return {name:values[wire] for name,wire in packet['named_registers'].items()}


def direct_values(inputs,modulus):
    """Evaluate the independently typeset cut equations in their own order."""
    values = {k:v % modulus for k,v in inputs.items()}
    expected = expected_named_cuts()
    for name,formula in expected.items():
        total=0
        for monomial,coefficient in formula.t.items():
            term=coefficient
            for ref in monomial:
                term=term*values[ref] % modulus
            total=(total+term) % modulus
        values[name]=total
    return {name:values[name] for name in expected}


def authenticated_modular_diagnostics(packet):
    binding_path = ROOT/'coefficients'/'UPSTREAM_BINDING.json'
    binding = json.loads(binding_path.read_text())
    values, records = {}, {}
    for name,entry in binding['ports'].items():
        path = ROOT/'coefficients'/entry['gzip_payload']
        compressed = path.read_bytes()
        raw = gzip.decompress(compressed)
        digest = hashlib.sha256(raw).hexdigest()
        require(digest == entry['sha256'], 'Coefficient raw hash: '+name)
        require(hashlib.sha256(compressed).hexdigest() == entry['gzip_sha256'],
                'Coefficient compressed hash: '+name)
        value = int.from_bytes(raw,'little')
        require(value.bit_length() == entry['bits'], 'Coefficient bit length')
        require(len(raw) == entry['raw_bytes'], 'Coefficient byte count')
        values[name] = value
        records[name] = {'bits':value.bit_length(),'raw_sha256':digest}
    require(values['beta']+1 == 1 << 590069, 'Wrong compact44 beta')
    require(values['K0']>=1 and 0<values['MC']<values['beta'] and
            0<values['MF']<2*values['beta'], 'Required fixed-port inequalities')
    rng=random.Random(20261024)
    cases=0
    for modulus in (1000003,1000033,2147483647):
        fixed={k:v%modulus for k,v in values.items()}
        for _ in range(24):
            inputs=dict(fixed)
            inputs.update({v:rng.randrange(modulus) for v in packet['variables']})
            require(literal_values(packet,inputs,modulus)==
                    direct_values(inputs,modulus), 'Actual-port modular disagreement')
            cases+=1
    return {'assignments':cases,'named_registers_per_assignment':
            len(packet['named_registers']),'moduli':[1000003,1000033,2147483647],
            'coefficients':records,'status':'diagnostic agreement'}


def reject_mutated_norm(packet, reference):
    mutated=deepcopy(packet)
    found=False
    for row in mutated['source']:
        if row[1]=='*' and 64 in row[2:]:
            row[row.index(64,2)]=63
            found=True
            break
    require(found,'Could not locate the intended mutation')
    # The corrupted graph remains topological, fully live, same degree upper
    # bound and same operation count. Its exact norm identity must reject it.
    audit_graph(mutated)
    try:
        check_literal_norm(mutated,reference)
    except ValueError:
        return {'mutation':'final coefficient 64 -> 63',
                'same_operations':True,'rejected_by':'exact conjugate-product identity'}
    raise ValueError('Norm corruption was not rejected')


def main():
    path=ROOT/'generated'/'p10_positive.json'
    packet=json.loads(path.read_text())
    graph=audit_graph(packet)
    reference,root_terms=norm_from_linear_factors()
    require(compact_norm()==reference,'Compact norm differs from sixteen factors')
    cut_count=check_all_cuts(packet)
    check_literal_norm(packet,reference)
    degree=check_degree(packet,reference,graph)
    diagnostic=authenticated_modular_diagnostics(packet)
    negative=reject_mutated_norm(packet,reference)
    result={
        'status':'PASS',
        'method':'Independent standard-library sparse integer polynomial arithmetic',
        'circuit_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'universal_norm':{'linear_factors':16,'expanded_root_terms':root_terms,
                          'cleared_polynomial_terms':len(reference.t),'exact':True},
        'named_cut_identities':cut_count,
        'graph':graph,'degree':degree,
        'actual_coefficient_modular_diagnostics':diagnostic,
        'negative_control':negative,
        'limitations':'Finite exact algebra and diagnostics; no proof search, '
                      'native compiler validation or ZFC consistency test.'}
    output=ROOT/'generated'/'INDEPENDENT_CHECKS.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
