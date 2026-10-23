#!/usr/bin/env python3
"""Independent finite checks for the two-root ten-integer polynomial.

Standard library only.  Does not import the builder or circuit library.
This verifies a literal arithmetic artifact, not the semantic K215 endpoint.
"""
from pathlib import Path
from collections import Counter, defaultdict
from itertools import combinations_with_replacement
from math import factorial, isqrt
import gzip
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parent
load = lambda name: json.loads((ROOT / name).read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()


def payloads():
    binding = load('data/coefficients_binding.json')
    ans = []
    for row in binding['files']:
        packed = (ROOT / 'data' / (row['name'] + '.bin.gz')).read_bytes()
        assert sha(packed) == row['gzip_sha256']
        raw = gzip.decompress(packed)
        value = int.from_bytes(raw, 'little')
        assert len(raw) == row['bytes']
        assert sha(raw) == row['sha256']
        assert value.bit_length() == row['bit_length']
        ans.append(value)
    assert [r['name'] for r in binding['files']] == ['beta', 'K', 'MC', 'MF_source']
    for row in load('SOURCE_PINS.json')['files']:
        assert sha((ROOT / row['local_path']).read_bytes()) == row['sha256']
    return ans


def source_check(source, records, code, ports):
    assert source['domain'] == 'strictly positive integers'
    assert len(source['variables']) == 31
    assert len(source['equations']) == 22
    assert records['variables'] == source['variables']
    assert records['ports'] == source['constants']
    assert records['source_sha256'] == sha((ROOT/'data/parent_quartic31.json').read_bytes())
    expected = {}
    for j, equation in enumerate(source['equations'], 1):
        groups = defaultdict(lambda: defaultdict(int))
        for row in equation['terms']:
            powers = tuple(row['powers'])
            alpha, fixed = powers[:31], powers[31:]
            assert len(fixed) == 4 and sum(alpha) <= 2
            weight = factorial(2-sum(alpha))
            for e in alpha:
                weight *= factorial(e)
            groups[alpha][fixed] += weight*row['coefficient']
        expected[j] = {a: tuple(sorted((p, c) for p, c in recipe.items() if c))
                       for a, recipe in groups.items()}
    record_list = []
    mass = 0
    for j, block in zip(code['order'], records['blocks']):
        assert block['source_equation'] == j
        got = {}
        for row in block['records']:
            alpha = tuple(row['alpha'])
            recipe = tuple((tuple(r['powers']), r['coefficient']) for r in row['recipe'])
            assert alpha not in got
            got[alpha] = recipe
            ref = row['coefficient']
            if 'literal' in ref:
                assert recipe == (((0, 0, 0, 0), ref['literal']),)
            else:
                assert records['recipes'][ref['fixed']] == row['recipe']
            value = 0
            for powers, coefficient in recipe:
                term = coefficient
                for p, e in zip(ports, powers):
                    term *= p**e
                value += term
            assert value != 0
            mass += abs(value)
            record_list.append((j, alpha, recipe))
        assert got == expected[j]
    assert len(record_list) == 94
    assert len(records['recipes']) == 10
    assert mass <= (1 << 2134927)
    weights = code['weights']
    assert weights[0] == 0 and len(weights) == 32
    assert len(set(weights)) == 32 and max(weights) == 183
    pairs = []
    for i, k in combinations_with_replacement(range(32), 2):
        alpha = [0]*31
        if i:
            alpha[i-1] += 1
        if k:
            alpha[k-1] += 1
        pairs.append((weights[i]+weights[k], tuple(alpha), 1 if i == k else 2))
    assert len(pairs) == 528

    def interactions(targets):
        target_for = dict(zip(code['order'], targets))
        owner = dict(zip(targets, code['order']))
        assert len(owner) == 22
        bad, hits = [], []
        for j, alpha, recipe in record_list:
            reverse = target_for[j]-sum(w*e for w,e in zip(weights[1:], alpha))
            assert reverse >= 0
            for e, word_alpha, multiplicity in pairs:
                q = reverse+e
                if q not in owner:
                    continue
                if owner[q] != j or word_alpha != alpha:
                    bad.append({'source_row':j, 'target_row':owner[q],
                                'source_alpha':alpha, 'word_alpha':word_alpha})
                else:
                    weight = factorial(2-sum(alpha))
                    for power in alpha:
                        weight *= factorial(power)
                    assert weight*multiplicity == 2
                    hits.append((j, alpha))
        return bad, hits

    bad, hits = interactions(code['targets'])
    assert not bad, bad
    assert len(hits) == 94
    legacy = load('parameters_shifted_legacy.json')
    old_bad, _ = interactions(legacy['targets'])
    assert len(old_bad) == 5, old_bad
    max_reverse = max(dict(zip(code['order'], code['targets']))[j]-
                      sum(w*e for w,e in zip(weights[1:], alpha))
                      for j, alpha, recipe in record_list)
    assert max_reverse == 5102
    leaders = [(j, alpha, recipe) for j, alpha, recipe in record_list
               if dict(zip(code['order'], code['targets']))[j]-
                  sum(w*e for w,e in zip(weights[1:], alpha)) == max_reverse]
    assert len(leaders) == 1 and leaders[0][2] == (((0,0,0,0),1),)
    # Positive tuple all ones is not a source zero: residual 5 is exactly one.
    row5 = source['equations'][4]
    assert all(not any(r['powers'][31:]) for r in row5['terms'])
    assert sum(r['coefficient'] for r in row5['terms']) == 1
    return dict(records=94, pair_monomials=528, interaction_checks=94*528,
                coefficient_mass_bit_length=mass.bit_length(),
                reversed_degree=max_reverse, leading_coefficient=1,
                old_target_failures=old_bad)


def fixed_mod(records, ports, modulus):
    out = {}
    for name, rows in records['recipes'].items():
        total = 0
        for row in rows:
            term = row['coefficient']
            for value, power in zip(ports, row['powers']):
                term = term*pow(value, power, modulus) % modulus
            total += term
        out[name] = total % modulus
    out['beta_source'] = pow(2, 2134940, modulus)
    out['beta_mask'] = pow(2, 2134919, modulus)
    return out


def dag_check(body):
    assert body['domain'] == 'Z'
    assert body['variables'] == ['f','g','h','k','l','w','x','y','z','m']
    counts = Counter()
    variables, fixed, degrees = [], [], []
    for i, node in enumerate(body['nodes']):
        kind = node['kind']
        counts[kind] += 1
        if kind == 'variable':
            variables.append(node['name']); degree = 1
        elif kind in ('fixed', 'literal'):
            if kind == 'fixed':
                fixed.append(node['name'])
            else:
                assert isinstance(node['value'], int)
            degree = 0
        else:
            assert kind in ('add','sub','mul')
            assert 0 <= node['left'] < i and 0 <= node['right'] < i
            a,b = degrees[node['left']], degrees[node['right']]
            degree = a+b if kind == 'mul' else max(a,b)
        degrees.append(degree)
    assert set(variables) == set(body['variables']) and len(variables) == 10
    assert len(fixed) == len(set(fixed)) == 12
    live, todo = set(), [body['output']]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        n = body['nodes'][i]
        if n['kind'] in ('add','sub','mul'):
            todo.extend([n['left'], n['right']])
    assert live == set(range(len(body['nodes'])))
    assert degrees[body['output']] == body['degree_upper_bound'] == 9152284
    assert {name:degrees[i] for name,i in body['named_nodes'].items()} == body['named_degrees']
    gates = {k:counts[k] for k in ('add','sub','mul')}
    assert gates == body['operation_counts'] and sum(gates.values()) == 586
    return degrees, dict(counts), gates


def evaluate_dag(body, fixed, values, modulus):
    out = []
    for n in body['nodes']:
        kind = n['kind']
        if kind == 'variable':
            v = values[n['name']]
        elif kind == 'fixed':
            v = fixed[n['name']]
        elif kind == 'literal':
            v = n['value']
        else:
            a,b = out[n['left']], out[n['right']]
            v = a+b if kind == 'add' else a-b if kind == 'sub' else a*b
        out.append(v % modulus)
    return {name:out[i] for name,i in body['named_nodes'].items()}


def direct(values, records, code, fixed, modulus):
    """Direct displayed formulas, independent of the Horner gate construction."""
    out = {}
    def keep(name, value):
        out[name] = value % modulus
        return out[name]
    t,g0,h0,k0,l,w,x,y,z,m = (values[k] for k in ('f','g','h','k','l','w','x','y','z','m'))
    b=keep('b',6*t+4)
    g=keep('packed_g',b*g0)
    h=keep('residue_h',b*h0)
    k=keep('residue_k',b*(3*k0+2))
    base=keep('base',fixed['beta_source']*b*b)
    top=keep('top',pow(base,183,modulus))
    ell=keep('ell',sum(pow(base,e,modulus) for e in code['weights'][1:]))
    target=keep('target',sum(pow(base,e,modulus) for e in code['targets']))
    dc=0
    for q,block in zip(code['targets'],records['blocks']):
        for row in block['records']:
            ref=row['coefficient']
            coefficient=ref['literal'] if 'literal' in ref else fixed[ref['fixed']]
            e=q-sum(w*a for w,a in zip(code['weights'][1:],row['alpha']))
            dc += coefficient*pow(base,e,modulus)
    dc=keep('Dcode',dc)
    n0=keep('N0',pow(base,184,modulus))
    n1=keep('N1',pow(base,5557,modulus))
    nn=keep('N',pow(base,5741,modulus))
    mc=keep('Mcode',n0-1-(b-1)*ell)
    tc=keep('Tcode',mc+(base-2)*target*n0)
    jc=keep('Jcode',2*(1+ell+g)**2*dc+target)
    sc=keep('Scode',g+jc*n0)
    xx=keep('X',nn*nn+(sc+tc)*nn+nn-1-sc)
    yy=keep('Y',pow(fixed['beta_source'],15,modulus)*fixed['beta_mask']*
            pow(base,5931,modulus)*b)
    cap=keep('Ccap',b*top)
    ll=keep('Lsmall',l*yy)
    uh=keep('Uhalf',ll*xx)
    u=keep('U',2*ll*xx)
    v=keep('V',4*g*w*yy)
    ww=keep('Wsmall',b*w)
    aa=keep('A',u*(v+1))
    bb=keep('Bsmall',2*xx+1)
    cc=keep('C',bb+(aa-2)*h)
    phalf=keep('Phalf',ll*xx*u*v)
    pn=keep('Pn',u*u*v)
    kk=keep('K',xx+1+k*(pn-2))
    ss=keep('Ssmall',2*aa-5)
    tt=keep('Tsmall',3*ww*cc-2*(ww*ww-1))
    q=keep('Q2',(phalf*phalf-1)*kk*kk+1)
    delta=keep('Delta',8*cap**3*g*kk*kk-g*g*(32*(cc-kk*ll)**2*cap**3+g*g*kk*kk))
    keep('O0',delta)
    xi=keep('xi',z*x)
    dd=keep('D',(aa*aa-4)*cc*cc+4)
    ee=keep('E',cc*cc*dd*xi)
    ff=keep('F',4*(aa*aa-4)*ee*ee+1)
    gs=keep('Gstar',2*(aa+2)*(aa-2)**2*ee*ee-1)
    om=keep('Omega',16*ee)
    hs=keep('Hstar',cc+(bb-cc)*ff+om*ff*y)
    ii=keep('Istar',(gs*gs-1)*hs*hs+1)
    sigma=keep('Sigma',xi*ss**5)
    argument=keep('merger_argument',tt+ss*y)
    theta=keep('Theta',(argument**3-argument*ss*ss-ss**3)*(argument**2+23*ss*ss))
    seed=keep('seed',b*q)
    a=keep('r0',seed+(3*delta-1)*(seed*z)**2)
    d=keep('r1',dd*ff*ii)
    center=keep('norm_center',sigma*m-theta)
    inner=keep('norm_inner',center*center-sigma*sigma*(a+d))
    keep('F10',inner*inner-4*sigma**4*a*d)
    return out


def leading_certificate(body, degrees, records, ports):
    result = []
    for p in (1000003,1000033,1000037):
        assert all(p % n for n in range(2,isqrt(p)+1))
        fixed=fixed_mod(records,ports,p)
        coefficients=[]
        for i,n in enumerate(body['nodes']):
            kind=n['kind']
            if kind=='variable': value=1
            elif kind=='fixed': value=fixed[n['name']]
            elif kind=='literal': value=n['value']
            else:
                j,k=n['left'],n['right']
                if kind=='mul': value=coefficients[j]*coefficients[k]
                else:
                    a=coefficients[j] if degrees[j]==degrees[i] else 0
                    b=coefficients[k] if degrees[k]==degrees[i] else 0
                    value=a+b if kind=='add' else a-b
            coefficients.append(value%p)
        assert coefficients[body['output']] != 0
        result.append(dict(prime=p,degree=degrees[body['output']],
                           diagonal_top_coefficient=coefficients[body['output']]))
    return result


def polynomial_identities():
    # A tiny exact multivariate polynomial ring, independent of the DAG builder.
    def add(a,b,sgn=1):
        out=dict(a)
        for key,value in b.items(): out[key]=out.get(key,0)+sgn*value
        return {k:v for k,v in out.items() if v}
    def mul(a,b):
        out=defaultdict(int)
        for x,c in a.items():
            for y,d in b.items():out[tuple(i+j for i,j in zip(x,y))]+=c*d
        return {k:v for k,v in out.items() if v}
    def scale(a,n):return {k:n*v for k,v in a.items() if n*v}
    def sq(a):return mul(a,a)
    q={(1,0,0):1};a={(0,1,0):1};d={(0,0,1):1}
    norm=add(sq(add(add(sq(q),a,-1),d,-1)),scale(mul(a,d),4),-1)
    # Numerator identity used to extract each rational square root.
    for first,second in ((a,d),(d,a)):
        lhs=add(sq(add(add(sq(q),first),second,-1)),scale(mul(sq(q),first),4),-1)
        assert lhs==norm
    # The four factors with formal square roots u,v.
    product={(0,0,0):1}
    for e in (-1,1):
        for f in (-1,1):product=mul(product,add(add(q,scale(a,e)),scale(d,f)))
    substituted={(i,2*j,2*k):c for (i,j,k),c in norm.items()}
    assert product==substituted
    return dict(exact_identities=3,norm_expanded_terms=len(norm))


def main():
    ports=payloads()
    source=load('data/parent_quartic31.json')
    records=load('generated/source_records.json')
    body=load('generated/signed10_b2.json')
    code=load('code_positive.json')
    source_report=source_check(source,records,code,ports)
    degrees,counts,gates=dag_check(body)
    lead=leading_certificate(body,degrees,records,ports)
    identities=polynomial_identities()
    rng=random.Random(20261023)
    probes=[dict.fromkeys(body['variables'],v) for v in (0,1,-1,2,-2)]
    probes += [dict(zip(body['variables'],[rng.randrange(-12,13) for _ in range(10)]))
               for _ in range(64)]
    evaluations=0
    for modulus in (1000003,1000033,1000037,65536):
        fixed=fixed_mod(records,ports,modulus)
        for values in probes:
            actual=evaluate_dag(body,fixed,values,modulus)
            expected=direct(values,records,code,fixed,modulus)
            assert actual==expected
            evaluations+=1
    for values in probes:
        b=6*values['f']+4
        modulus=12*b*b
        v=direct(values,records,code,fixed_mod(records,ports,modulus),modulus)
        assert (v['X']+1)%abs(b)==0
        assert v['X']%2==1 and v['X']%3==0
        assert v['K']%abs(b)==0 and v['K']%3==0
        assert v['Q2']%(b*b)==1 and v['Q2']%3==1
        assert (v['C']+1)%(2*abs(b))==0
        assert v['D']%(4*abs(b))==0
        assert v['r0']%(2*abs(b))==abs(b)
        assert v['r1']%(2*abs(b))==0
    report=dict(status='PASS',semantic_scope='finite artifact checks; inherited endpoint is a theorem dependency',
                circuit_sha256=sha((ROOT/'generated/signed10_b2.json').read_bytes()),
                node_counts=counts,operation_counts=gates,total_operations=sum(gates.values()),
                exact_degree=9152284,degree_certificates=lead,source=source_report,
                modular_direct_formula_assignments=evaluations,
                modular_named_register_comparisons=evaluations*len(body['named_nodes']),
                congruence_assignments=len(probes),identities=identities)
    (ROOT/'generated/VERIFIED.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','total_operations','exact_degree',
                                          'degree_certificates','modular_named_register_comparisons')}))


if __name__=='__main__':
    main()
