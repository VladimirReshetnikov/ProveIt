#!/usr/bin/env python3
"""Independent inert-JSON and exact-polynomial audit, authored 2026-10-04.

Does not import or execute the certificate emitter, predecessor code, saved
programs, simulators, or earlier checkers. Standard library only. The intended
identities below are independently transcribed mathematical formulas. Source
ASTs are parsed only for a mechanical, alpha-renamed POWER comparison.
"""
import ast
import copy
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'matrix-chronological-certificate-20261004'
VARIANTS = ('three-input-linear', 'one-input-linear',
            'three-input-quartic', 'one-input-quartic')
DOMAIN = 'Every input and every witness leaf is an ordinary strictly positive integer.'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def load_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object,
                      parse_constant=lambda value: need(False, 'nonfinite JSON ' + value))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Poly:
    """Sparse Z-polynomial. Monomials are sorted tuples of leaf names."""
    def __init__(self, terms):
        self.terms = {m: c for m, c in terms.items() if c}
    @staticmethod
    def cast(value):
        if isinstance(value, Poly):
            return value
        need(type(value) is int, 'polynomial coefficient is not an integer')
        return Poly({(): value})
    @staticmethod
    def variable(name):
        return Poly({(name,): 1})
    def __add__(self, value):
        other = self.cast(value)
        result = self.terms.copy()
        for m, c in other.terms.items():
            result[m] = result.get(m, 0) + c
        return Poly(result)
    __radd__ = __add__
    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})
    def __sub__(self, value):
        return self + -self.cast(value)
    def __rsub__(self, value):
        return self.cast(value) + -self
    def __mul__(self, value):
        other = self.cast(value)
        result = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in other.terms.items():
                m = tuple(sorted(m1 + m2))
                result[m] = result.get(m, 0) + c1 * c2
        return Poly(result)
    __rmul__ = __mul__
    def __pow__(self, n):
        need(type(n) is int and n >= 0, 'bad polynomial power')
        result = self.cast(1)
        for _ in range(n):
            result = result * self
        return result
    def __eq__(self, value):
        return self.terms == self.cast(value).terms
    def degree(self):
        return max(map(len, self.terms), default=-1)
    def digest(self):
        normalized = [[list(m), c] for m, c in sorted(self.terms.items())]
        return hashlib.sha256(json.dumps(normalized, separators=(',', ':')).encode()).hexdigest()


def intended(variant):
    """Independent mathematical specification, not a gate-emitting program."""
    one = variant.startswith('one-input')
    quartic = variant.endswith('quartic')
    witnesses, residuals, ports, modules, domains = [], {}, {}, [], {}
    def positive(name):
        need(name not in witnesses, 'duplicate specification variable')
        witnesses.append(name)
        domains[name] = 'positive integer leaf'
        return Poly.variable('w:' + name)
    def natural(name):
        return positive(name + '.Plus') - 1
    def signed(name):
        return positive(name + '.Positive') - positive(name + '.Negative')
    def equation(name, left, right):
        need(name not in residuals, 'duplicate specification equation')
        residuals[name] = Poly.cast(left) - right
    def power(prefix, base, exponent):
        z = positive(prefix + '.out')
        a = positive(prefix + '.aMinus1') + 1
        beta = positive(prefix + '.betaMinus1') + 1
        p = {key: positive(prefix + '.' + key) for key in
             ('w', 'M', 'g', 'x', 'y', 'u', 'v', 's', 't', 'qb', 'qv', 'strict')}
        d = {key: natural(prefix + '.' + key) for key in
             ('dwb', 'dwk', 'dyk', 'alpha1', 'alpha2', 'sigma1', 'sigma2',
              'tau1', 'tau2', 'rho1', 'rho2')}
        w, M, g, x, y, u, v, s, t, qb, qv, strict = (
            p[key] for key in ('w', 'M', 'g', 'x', 'y', 'u', 'v', 's', 't', 'qb', 'qv', 'strict'))
        k, m = exponent + 1, base * z
        eqs = [
            (x**2, 1 + (a**2 - 1)*y**2),
            (u**2, 1 + (a**2 - 1)*v**2),
            (s**2, 1 + (beta**2 - 1)*t**2),
            (beta, 1 + 4*y*qb),
            (beta + u*d['alpha1'], a + u*d['alpha2']),
            (v, y**2*qv),
            (s + u*d['sigma1'], x + u*d['sigma2']),
            (t + 4*y*d['tau1'], k + 4*y*d['tau2']),
            (y, k + d['dyk']),
            (w, base + d['dwb']),
            (w, k + d['dwk']),
            (M, m + strict),
            (a**2, 1 + ((w + 1)**2 - 1)*(w*g)**2),
            (2*a*base, M + base**2 + 1),
            (x + M*d['rho1'], y*(a - base) + m + M*d['rho2']),
        ]
        for j, (left, right) in enumerate(eqs, 1):
            equation(prefix + '.eq' + str(j), left, right)
        modules.append(dict(name=prefix, base=Poly.cast(base), exponent=exponent, out=z))
        return z
    if one:
        g1, g2, g3 = [positive('gap.' + str(j)) for j in (1, 2, 3)]
        inner = natural('decode.inner')
        equation('decode.inner_cantor', 2*inner, (g2+g3-2)*(g2+g3-1)+2*(g3-1))
        equation('decode.outer_cantor', 2*(Poly.variable('i:code')-1),
                 (g1-1+inner)*(g1+inner)+2*inner)
        ports['inner_code'] = inner
    else:
        g1, g2, g3 = [Poly.variable('i:g' + str(j)) for j in (1, 2, 3)]
    D, x, y = g1+g2+g3, g1, g1+g2
    A, B = 3*x-D, 3*y-2*D
    delta = natural('radius.delta')
    equation('radius.nonnegative', 4*D**2, 205*(A**2+B**2)+delta)
    U, V = 6*A-13*B, 13*A+6*B
    h, q = positive('fraction.h'), positive('fraction.q')
    u, v = signed('fraction.u'), signed('fraction.v')
    c1, c2, c3 = [signed('bezout.' + str(j)) for j in (1, 2, 3)]
    equation('fraction.real', U, h*u)
    equation('fraction.imag', V, h*v)
    equation('fraction.denominator', 2*D, h*q)
    equation('fraction.primitive', c1*u+c2*v+c3*q, 1)
    n = natural('valuation.n')
    P = power('power5', 5, n)
    r, k, s = positive('valuation.r'), natural('valuation.k'), positive('valuation.s')
    equation('valuation.decompose', q, P*r)
    equation('valuation.remainder', r, 5*k+s)
    if quartic:
        equation('valuation.nonzero_remainder', (s-1)*(s-2)*(s-3)*(s-4), 0)
    else:
        t = positive('valuation.t')
        equation('valuation.nonzero_remainder', s+t, 5)
        ports['remainder_complement'] = t
    b = 4*P+1
    Bexp = 3+4*b
    T = power('power_complex', Bexp, n)
    C, S = signed('complex.C'), signed('complex.S')
    bounds = [natural('complex.bound.'+str(j)) for j in (1, 2, 3, 4)]
    equation('complex.C_lower', C+P, bounds[0])
    equation('complex.C_upper', P-C, bounds[1])
    equation('complex.S_lower', S+P, bounds[2])
    equation('complex.S_upper', P-S, bounds[3])
    kappa = signed('complex.quotient')
    equation('complex.remainder', T-C-b*S, kappa*(b**2+1))
    accepted = positive('acceptance.positive')
    equation('acceptance.strict', delta**2+(r-1)**2+(u-C)**2+(v+S)**2, accepted)
    ports.update(dict(g1=g1,g2=g2,g3=g3,D=D,x=x,y=y,A=A,B=B,delta=delta,U=U,V=V,
                      h=h,q=q,u=u,v=v,bezout1=c1,bezout2=c2,bezout3=c3,
                      n=n,P=P,r=r,k=k,s=s,radix=b,power_base=Bexp,T=T,C=C,S=S,
                      kappa=kappa,acceptance_positive=accepted))
    return witnesses, residuals, ports, modules, domains


def audit(dag):
    variant = dag['variant']
    need(variant in VARIANTS, 'unknown variant')
    need(dag['schema'] == 'fixed-positive-integer-polynomial-dag-v1', 'wrong schema')
    need(dag['domain'] == DOMAIN, 'positive-integer domain changed')
    expected_inputs = ['code'] if variant.startswith('one-input') else ['g1','g2','g3']
    need(dag['inputs'] == expected_inputs, 'wrong inputs')
    witnesses, expected, expected_ports, expected_modules, domains = intended(variant)
    need(dag['witnesses'] == witnesses, 'witness declarations/order mismatch')
    need(len(set(witnesses)) == len(witnesses), 'duplicate witness')
    polys = {kind+name: Poly.variable(kind+name) for kind,names in
             (('i:',dag['inputs']),('w:',witnesses)) for name in names}
    degrees = {key: 1 for key in polys}
    def ref(name, before):
        need(isinstance(name,str), 'reference is not text')
        if name.startswith('c:'):
            need(re.fullmatch(r'c:(0|-?[1-9][0-9]*)', name) is not None, 'noncanonical integer literal')
            return Poly.cast(int(name[2:]))
        if name.startswith('g:'):
            need(re.fullmatch(r'g:(0|[1-9][0-9]*)',name) is not None, 'noncanonical gate reference')
            need(int(name[2:]) < before, 'forward or invalid gate reference: '+name)
        need(name in polys, 'unknown reference: '+name)
        return polys[name]
    def syntactic(name):
        return 0 if name.startswith('c:') else degrees[name]
    gates = dag['gates']
    for j, gate in enumerate(gates):
        need(type(gate) is list and len(gate) == 3, 'invalid gate shape')
        op, ar, br = gate
        need(op in ('+','-','*'), 'invalid gate operator')
        a,b = ref(ar,j), ref(br,j)
        value = a+b if op=='+' else a-b if op=='-' else a*b
        polys['g:'+str(j)] = value
        degrees['g:'+str(j)] = syntactic(ar)+syntactic(br) if op=='*' else max(syntactic(ar),syntactic(br))
    output = ref(dag['output'],len(gates))
    body = dag['body_gate_count']
    need(type(body) is int and 0 <= body <= len(gates), 'bad body gate count')
    equations = dag['equations']
    need([e[0] for e in equations] == list(expected), 'missing/changed/reordered equation')
    residuals = {}
    for name, left, right in equations:
        actual = ref(left,body)-ref(right,body)
        need(actual == expected[name], 'equation mismatch: '+name)
        residuals[name] = actual
    need(set(dag['ports']) == set(expected_ports), 'port names mismatch')
    for name,value in expected_ports.items():
        need(ref(dag['ports'][name],body) == value, 'port mismatch: '+name)
    need(len(dag['modules']) == 2, 'wrong POWER module count')
    for actual, goal in zip(dag['modules'],expected_modules):
        need(actual['name']==goal['name'] and actual['kind']=='POWER', 'module name/kind mismatch')
        for key in ('base','exponent','out'):
            need(ref(actual[key],body) == goal[key], 'POWER argument mismatch: '+key)
    # Check actual final circuit topology, not only equality of polynomials.
    expected_tail, square_refs = [], []
    for _,left,right in equations:
        r = 'g:'+str(body+len(expected_tail))
        expected_tail.append(['-',left,right])
        sq = 'g:'+str(body+len(expected_tail))
        expected_tail.append(['*',r,r])
        square_refs.append(sq)
    out = square_refs[0]
    for sq in square_refs[1:]:
        new = 'g:'+str(body+len(expected_tail))
        expected_tail.append(['+',out,sq])
        out = new
    need(gates[body:] == expected_tail and dag['output'] == out, 'not the complete literal sum of squares')
    expected_output = sum((p*p for p in expected.values()), Poly.cast(0))
    need(output == expected_output, 'full normalized polynomial mismatch')
    live, pending = set(), [dag['output']]
    while pending:
        name = pending.pop()
        if name in live:
            continue
        live.add(name)
        if name.startswith('g:'):
            pending.extend(gates[int(name[2:])][1:])
    required = list(polys)
    dead = [name for name in required if name not in live]
    need(not dead, 'dead input/witness/gate: '+repr(dead))
    expected_region_names = ('input_decode','radius','primitive_gaussian_fraction',
        'valuation_exponent','power5','valuation','extraction_base','power_complex',
        'bounded_complex_remainder','acceptance','sum_of_squares')
    need(tuple(r['name'] for r in dag['regions']) == expected_region_names, 'region labels mismatch')
    one = variant.startswith('one-input')
    quartic = variant.endswith('quartic')
    expected_region_sizes = dict(zip(expected_region_names,
        [(4 if one else 0,2 if one else 0),(1,1),(12,4),(1,0),(26,15),
         (3 if quartic else 4,3),(0,0),(26,15),(10,5),(1,1),(0,0)]))
    previous = [0,0,0]
    regions = []
    for region in dag['regions']:
        limits = [region[k] for k in ('witness_range','gate_range','equation_range')]
        need(all(type(r) is list and len(r)==2 and all(type(v) is int for v in r) for r in limits), 'bad region intervals')
        need(all(r[0]==p and r[0]<=r[1] for r,p in zip(limits,previous)), 'noncontiguous region intervals')
        previous = [r[1] for r in limits]
        (w0,w1),(g0,g1),(e0,e1) = limits
        need((w1-w0,e1-e0)==expected_region_sizes[region['name']], 'wrong region witness/equation allocation')
        need(w1<=len(witnesses) and g1<=len(gates) and e1<=len(equations), 'region out of bounds')
        regions.append(dict(name=region['name'],positive_witnesses=w1-w0,equations=e1-e0,
                            gates=g1-g0,operations=dict(Counter(g[0] for g in gates[g0:g1]))))
    need(previous == [len(witnesses),len(gates),len(equations)], 'regions omit final entries')
    for prefix in ('power5','power_complex'):
        region = next(r for r in regions if r['name']==prefix)
        need(region['positive_witnesses']==26 and region['equations']==15, 'POWER source size mismatch')
        monomial = tuple(sorted(['w:'+prefix+'.w']*4+['w:'+prefix+'.g']*2))
        need(residuals[prefix+'.eq13'].terms.get(monomial)==-1, 'missing residual degree-six term')
        need(output.terms.get(tuple(sorted(monomial*2)))==1, 'missing degree-twelve square term')
    need(output.degree()==12 and degrees[dag['output']]==12, 'degree is not exactly twelve')
    return dict(variant=variant,inputs=len(dag['inputs']),positive_witnesses=len(witnesses),
        equations=len(equations),outer_equations=len(equations)-30,gates=len(gates),body_gates=body,
        operations=dict(Counter(g[0] for g in gates)),
        body_operations=dict(Counter(g[0] for g in gates[:body])),
        sos_operations=dict(Counter(g[0] for g in gates[body:])),regions=regions,
        dead_gates=0,dead_witnesses=0,dead_inputs=0,
        exact_residual_degrees={n:p.degree() for n,p in residuals.items()},
        exact_residual_degree_histogram=dict(Counter(p.degree() for p in residuals.values())),
        exact_final_degree=output.degree(),syntactic_final_degree_upper_bound=degrees[dag['output']],
        normalized_output_monomials=len(output.terms),normalized_output_sha256=output.digest(),
        normalized_residual_sha256={n:p.digest() for n,p in residuals.items()},
        source_leaf_domain=DOMAIN,POWER_calls=2,POWER_base_lower_bounds=[5,23],
        POWER_exponent_domain='valuation.n.Plus-1 is a nonnegative integer',
        verdict='PASS')


def power_ast_comparison():
    current = ast.parse((ROOT/'emit_certificate.py').read_text())
    prior_copy = ROOT/'sources/prior-build_certificate.py.txt'
    prior = ast.parse(prior_copy.read_text())
    def block(tree):
        cls = next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name=='Source')
        method = next(n for n in cls.body if isinstance(n,ast.FunctionDef) and n.name=='power')
        result = []
        for node in method.body:
            result.append(node)
            if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='equations' for t in node.targets):
                return ast.Module(body=result,type_ignores=[])
        raise ValueError('POWER equation list absent')
    class Rename(ast.NodeTransformer):
        mapping = {'name':'prefix','out':'z','pp':'p','nn':'d','delta':'dlt'}
        def visit_Name(self,node):
            node.id = self.mapping.get(node.id,node.id)
            return node
        def visit_Constant(self,node):
            if node.value=='modulus':
                node.value='M'
            return node
    old = Rename().visit(block(prior))
    new = block(current)
    need(ast.dump(old,include_attributes=False)==ast.dump(new,include_attributes=False),
         'POWER prelude/equations differ from prior after declared renaming')
    if (PRIOR/'build_certificate.py').exists():
        need(sha(PRIOR/'build_certificate.py')==sha(prior_copy), 'inert prior copy differs from original')
    need(sha(prior_copy)=='722db1e253ac3d241fdb538c46a86ffc15e6c208cb8116d168883b6c5bfaa799',
         'unexpected pinned prior source')
    return dict(verdict='PASS',scope='entire POWER prelude and all fifteen equation pairs',
                method='Python AST parse and literal comparison only; no evaluation or execution',
                renamings={'name':'prefix','out':'z','pp':'p','nn':'d','delta':'dlt','modulus witness suffix':'M'},
                prior_builder_sha256=sha(prior_copy))


def mutation_tests(originals):
    results = []
    for variant, original in originals.items():
        def run(label, change):
            corrupted = copy.deepcopy(original)
            change(corrupted)
            try:
                audit(corrupted)
            except (ValueError,KeyError,TypeError,IndexError) as error:
                results.append(dict(variant=variant,mutation=label,rejected=True,reason=str(error)))
            else:
                raise ValueError('mutation was accepted: '+variant+' '+label)
        run('missing outer equation',lambda d:d['equations'].pop(0))
        run('dead witness leaf',lambda d:d['witnesses'].append('injected.dead'))
        def coefficient(d):
            gate = next(g for g in d['gates'] if 'c:205' in g)
            gate[gate.index('c:205')] = 'c:204'
        run('changed radius coefficient 205 to 204',coefficient)
        run('invalid forward gate reference',lambda d:d['gates'][0].__setitem__(1,'g:999999'))
        run('changed leaf domain to nonnegative',lambda d:d.__setitem__('domain','All leaves are nonnegative integers.'))
        run('dropped final square from output',lambda d:d.__setitem__('output','g:'+str(len(d['gates'])-2)))
        def orientation(d):
            # Locate u-C and v+S structurally through final acceptance residual.
            final_left = d['equations'][-1][1]
            last_sum = d['gates'][int(final_left[2:])]
            dv_square = d['gates'][int(last_sum[2][2:])]
            dv = d['gates'][int(dv_square[1][2:])]
            need(dv == ['+',d['ports']['v'],d['ports']['S']], 'orientation mutation target absent')
            dv[0] = '-'
        run('wrong forbidden-orbit sign v-S',orientation)
        def power13(d):
            idx = next(i for i,e in enumerate(d['equations']) if e[0]=='power5.eq13')
            d['equations'][idx][2] = 'c:1'
        run('corrupted POWER equation thirteen',power13)
    return results


def main():
    results, originals, pins = [], {}, {}
    for variant in VARIANTS:
        path = ROOT/'evidence'/(variant+'.dag.json')
        dag = load_json(path)
        need(dag['variant']==variant, 'file variant mismatch')
        originals[variant] = dag
        result = audit(dag)
        result['dag_sha256'] = sha(path)
        results.append(result)
        pins[str(path.relative_to(ROOT))] = sha(path)
    comparison = power_ast_comparison()
    mutations = mutation_tests(originals)
    for path in [ROOT/'emit_certificate.py',ROOT/'review/ALGEBRA_REVIEW.md',
                 ROOT/'sources/POWER_SOURCE_NOTES.md',ROOT/'sources/prior-build_certificate.py.txt',
                 ROOT/'sources/pell-dependency.json',ROOT/'sources/pell-source.lean',
                 Path(__file__)]:
        pins[str(path)] = sha(path)
    receipt = dict(schema='report58-independent-expanded-dag-audit-v1',verdict='PASS',
        scope='Independent exact algebra and full expanded source audit; POWER semantics and geometry remain stated prior theorem dependencies.',
        execution='Only this new checker ran. Emitter, prior builders/checkers, physical simulators, and saved programs were not run or imported.',
        source_pins=pins,source_POWER_comparison=comparison,variants=results,
        mutation_tests=mutations,mutation_tests_rejected=len(mutations))
    (HERE/'audit-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(verdict=receipt['verdict'],variants=[{k:r[k] for k in
        ('variant','inputs','positive_witnesses','equations','gates','operations','exact_final_degree','normalized_output_monomials')}
        for r in results],mutations_rejected=len(mutations),POWER_source_match=comparison['verdict']),indent=2))


if __name__ == '__main__':
    main()
