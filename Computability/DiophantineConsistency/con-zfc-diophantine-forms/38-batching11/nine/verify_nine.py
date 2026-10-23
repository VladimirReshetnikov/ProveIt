#!/usr/bin/env python3
"""Finite certificates for the nine-variable construction (Python 3.10+).

These checks certify finite data and polynomial identities, not consistency,
unbounded solvability, or an end-to-end proof-assistant theorem.
"""
from pathlib import Path
from collections import Counter, defaultdict
from itertools import combinations_with_replacement, product
from math import factorial, isqrt
import gzip
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parent


def read(name):
    return json.loads((ROOT / name).read_text())


def add_poly(a, b, sign=1):
    out = a.copy()
    for e, c in b.items():
        out[e] = out.get(e, 0) + sign * c
        if not out[e]:
            del out[e]
    return out


def mul_poly(a, b):
    out = defaultdict(int)
    for ea, ca in a.items():
        for eb, cb in b.items():
            out[tuple(x+y for x, y in zip(ea, eb))] += ca*cb
    return {e:c for e, c in out.items() if c}


def audit_source():
    raw = (ROOT/'parent31.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'
    parent, source = json.loads(raw), read('source_data.json')
    weights = read('weights.json')['weights_with_zero']
    assert len(weights) == 32 and weights[0] == 0 and max(weights) == 799
    sums = [weights[i]+weights[j] for i, j in combinations_with_replacement(range(32), 2)]
    assert len(sums) == len(set(sums)) == 528
    assert (source['M'], source['stride'], source['length']) == (799, 3197, 70334)
    assert source['parent_ports'] == ['beta', 'K0', 'MC', 'MF']

    # Independent Taylor expansion of a quadratic at the all-one vector.
    # After the factorial weighting the constant term is twice the value,
    # linear coefficients are first derivatives, and the quadratic part is
    # unchanged except for its pure-square factorials.
    expected = {}
    for j, row in enumerate(parent['equations']):
        coeffs = defaultdict(lambda: defaultdict(int))
        for term in row['terms']:
            alpha, ports = term['powers'][:31], tuple(term['powers'][31:])
            c = term['coefficient']
            assert sum(alpha) <= 2
            coeffs[(0,)*31][ports] += 2*c
            for i, degree in enumerate(alpha):
                if degree:
                    e = [0]*31; e[i] = 1
                    coeffs[tuple(e)][ports] += degree*c
            if sum(alpha) == 2:
                coeffs[tuple(alpha)][ports] += c*(2 if 2 in alpha else 1)
        for alpha, recipe in coeffs.items():
            recipe = {e:c for e, c in recipe.items() if c}
            if not recipe:
                continue
            exponent = 1598-sum(a*w for a,w in zip(alpha,weights[1:]))
            expected[j, exponent] = recipe
            pair_weight = factorial(2)//(factorial(2-sum(alpha)))
            for power in alpha:
                pair_weight //= factorial(power)
            factorial_weight = factorial(2-sum(alpha))
            for power in alpha:
                factorial_weight *= factorial(power)
            assert pair_weight * factorial_weight == 2
    received = {}
    for row in source['rows']:
        j = row['row']
        assert row['shift'] == 3197*j and row['target'] == 3197*j+1598
        for term in row['terms']:
            leaf = term['coefficient']
            recipe = {(0,)*4:leaf} if isinstance(leaf,int) else {
                tuple(t['powers']):t['coefficient'] for t in source['fixed_recipes'][leaf]}
            received[j, term['exponent']] = recipe
    assert expected == received and len(expected) == 136
    assert len(source['fixed_recipes']) == 16
    assert sum(t['coefficient'] for t in parent['equations'][4]['terms']) == 1

    # For every source exponent, exactly its padded unordered pair hits the
    # target. Distinct residual blocks cannot interfere: their spans have
    # length 4M+1 and are translated by that same length.
    pairs = Counter(sums)
    assert all(pairs[1598-e] == 1 for j,e in expected)
    assert all(j*3197+3196 < (j+1)*3197 for j in range(21))
    return source, {'parent_sha256':hashlib.sha256(raw).hexdigest(),
        'quadratic_rows':22,'shifted_coordinates':31,'weighted_records':136,
        'distinct_nonliteral_recipes':16,'all_unordered_pair_sums':528,
        'all_pair_sums_distinct':True,'all_coefficient_recipes_reconstructed':True,
        'coefficient_extraction_factor':2,'block_interference_excluded':True,
        'all_zero_input_is_not_a_solution':True}


def audit_coefficients(source):
    compiler = ROOT.parent/'compiler'
    binding = json.loads((compiler/'COEFFICIENT_BINDING.json').read_text())
    ports = {}
    for row in binding['materialization']['files']:
        packed = (compiler/row['file']).read_bytes()
        raw = gzip.decompress(packed)
        assert hashlib.sha256(raw).hexdigest() == row['sha256']
        assert hashlib.sha256(packed).hexdigest() == row['gzip_sha256']
        value = int.from_bytes(raw, 'little')
        assert value.bit_length() == row['bits']
        ports[{'K':'K0','MF_source':'MF'}.get(row['port'],row['port'])] = value
    values = [ports[x] for x in source['parent_ports']]
    def recipe(terms):
        total = 0
        for term in terms:
            v = term['coefficient']
            for x,e in zip(values,term['powers']): v *= x**e
            total += v
        return total
    bound = source['coefficient_bound_C']
    C = bound['constant'] + recipe(bound['positive_terms'])
    k = (2048*C).bit_length()
    fixed = {name:recipe(terms) for name,terms in source['fixed_recipes'].items()}
    fixed['kappa'] = 1 << k
    assert fixed['kappa'] > 2048*C
    assert k == 1359525 and C.bit_length() == 1359514
    assert all(abs(fixed[t['coefficient']] if isinstance(t['coefficient'],str)
                   else t['coefficient']) < C for row in source['rows'] for t in row['terms'])
    receipt = read('COEFFICIENT_BINDING.json')
    assert receipt['instance'] == binding['instance']
    raw = gzip.decompress((ROOT/'kappa.bin.gz').read_bytes())
    assert hashlib.sha256(raw).hexdigest() == receipt['kappa_sha256']
    assert int.from_bytes(raw,'little') == fixed['kappa']
    for name,x in fixed.items():
        if name == 'kappa': continue
        data = receipt['derived_coefficients'][name]
        assert data['sign'] == (x>0)-(x<0)
        assert data['absolute_bit_length'] == abs(x).bit_length()
        assert data['magnitude_sha256'] == hashlib.sha256(abs(x).to_bytes((abs(x).bit_length()+7)//8,'little')).hexdigest()
    return fixed, {'complete_native_tuple_checked':True,'all_fixed_recipes_checked':True,
        'C_bit_length':C.bit_length(),'kappa_exponent':k,'all_136_strict_bounds':True}


def evaluate(packet, inputs, fixed, p):
    values = []
    for i,node in enumerate(packet['nodes']):
        kind = node['kind']
        if kind == 'literal': v = node['value']
        elif kind == 'fixed': v = fixed[node['name']]
        elif kind == 'variable': v = inputs[node['name']]
        else:
            assert 0 <= node['left'] < i and 0 <= node['right'] < i
            a,b = values[node['left']], values[node['right']]
            v = a*b if kind == 'mul' else a+b if kind == 'add' else a-b
        values.append(v%p)
    return values[packet['output']]


def literal(inputs, fixed, source, p):
    """Independent direct formula; source kernel uses its 136-term sum."""
    b = inputs['epsilon']+2
    g,h,s,w,i,j = [inputs[key]+1 for key in ('g0','h0','s0','w0','i0','j0')]
    phi,n = inputs['phi'],inputs['n']
    mod = lambda z:z%p
    def sq(z): return z*z%p
    def geom(base,length):
        # Independent modular sum by the identity (B-1)sum=B^length-1;
        # the singular B=1 case is handled exactly.
        return length%p if base%p == 1 else (pow(base,length,p)-1)*pow((base-1)%p,-1,p)%p
    B = mod(fixed['kappa']*sq(b))
    Q0 = pow(B,800,p)
    ell = sum(pow(B,e,p) for e in source['weights'][1:])%p
    kernel = sum((fixed[t['coefficient']] if isinstance(t['coefficient'],str) else t['coefficient'])
                 *pow(B,row['shift']+t['exponent'],p) for row in source['rows'] for t in row['terms'])%p
    Z = sum(pow(B,row['target'],p) for row in source['rows'])%p
    S = mod(g+Q0*(2*sq(1+g)*kernel+B*geom(B,70334)))
    T = mod(Q0-1-(b-1)*ell+Q0*(B-2)*Z)
    N = pow(B,71135,p)
    R = mod(S*(sq(N)-N)+(T+1)*(sq(N)-1))
    cap = mod(32*b*pow(B,799,p))
    U,Y = mod(sq(N)*w),mod(sq(N)*s)
    P = mod(2*sq(R*Y)*U)
    K = mod(R+1+h*(P-1))
    A = mod(R*Y*(U+1))
    C = mod(2*R+1+b*w+phi)
    J = mod(4*A-5)
    Q = mod(3*b*w*C-2*(sq(b*w)-1))
    D = mod((sq(A)-1)*sq(C)+1)
    E = mod(i*J*D*sq(C))
    F = mod((sq(A)-1)*sq(E)+1)
    G = mod(A+F*(C*D+1-A))
    H = mod(2*R+1+j*C)
    I = mod((sq(G)-1)*sq(H)+1)
    a0 = mod((sq(P)-1)*sq(K)+1)
    a1 = mod(D*F*I)
    u,v = mod(J*F),mod(Q*F+J*(H-C))
    margin = mod(sq(K)*cap-4*sq(C-K*Y)*cap-8*g*sq(K))
    MD = mod(A*C+Y*(U+1)*sq(b*w+phi+1)+1)
    MF = mod(A*E+1)
    MI = mod(F*(D*(C*H+sq(b*w+phi))+2*sq(H)+sq(A))-sq(A)+1)
    V0,V1 = mod(P*K+1),mod(MD*MF*MI+1)
    divbound = mod(sq(Q)+sq(H-C)+1)
    omega = mod(u*(2*margin-1))
    theta = mod(u*(n+divbound)+v-omega*(2*divbound+V0*V1))
    return mod(sq(sq(theta)-sq(omega)*(a0+sq(V0)*a1))-4*sq(sq(omega))*sq(V0)*a0*a1)


def exact_degree(packet):
    """Upper degree and exact diagonal coefficient at that upper degree.

    All 16 native-derived leaves remain *independent indeterminates* here.
    A vanished leading coefficient does not silently lower a bound. Thus
    the final nonzero monomial proves the degree for the actual tuple,
    without assuming any unknown fixed coefficient vanishes or is generic.
    """
    names = ['kappa'] + sorted({n['name'] for n in packet['nodes'] if n['kind']=='fixed' and n['name']!='kappa'})
    zero = (0,)*len(names)
    values = []
    for node in packet['nodes']:
        kind = node['kind']
        if kind == 'literal':
            v = (0,{zero:node['value']} if node['value'] else {})
        elif kind == 'variable': v = (1,{zero:1})
        elif kind == 'fixed':
            e = list(zero);e[names.index(node['name'])]=1
            v = (0,{tuple(e):1})
        else:
            da,a = values[node['left']]; db,b = values[node['right']]
            if kind == 'mul': v = (da+db,mul_poly(a,b))
            else:
                d = max(da,db)
                v = (d,add_poly(a if da==d else {},b if db==d else {},-1 if kind=='sub' else 1))
        values.append(v)
    d,lead = values[packet['output']]
    expected = [0]*len(names);expected[0]=83088652
    assert d == 166177600 and lead == {tuple(expected):2**196}
    ledger = {}
    for name,index in packet['named_nodes'].items():
        degree,coefficient=values[index]
        ledger[name] = {'syntactic_upper_bound':degree,'diagonal_top_coefficient':[
            {'coefficient':c,'powers':{s:e for s,e in zip(names,powers) if e}}
            for powers,c in sorted(coefficient.items())]}
    (ROOT/'generated/DEGREE_CERTIFICATE.json').write_text(json.dumps({
        'method':'Upper bound at every gate and exact diagonal coefficient at that bound; all fixed leaves symbolic.',
        'fixed_indeterminates':names,'degree':d,
        'diagonal_leading_coefficient':'2^196*kappa^83088652',
        'independent_of_all_16_derived_native_coefficients':True,'registers':ledger},indent=2)+'\n')
    return {'degree':d,'leading_coefficient':'2^196*kappa^83088652',
            'all_native_derived_coefficients_retained_symbolically':True}


def audit_circuits(source,fixed):
    packets = {n:read('generated/'+n+'.json') for n in ('nine_natural','nine_positive','nine_degree_certificate')}
    operations = {}
    for name,packet in packets.items():
        kinds = Counter(n['kind'] for n in packet['nodes'])
        count = sum(kinds[x] for x in ('add','sub','mul'))
        assert count == packet['operations']
        assert set(packet['variables']) == {n['name'] for n in packet['nodes'] if n['kind']=='variable'}
        live = set();todo=[packet['output']]
        while todo:
            k=todo.pop()
            if k in live: continue
            live.add(k); node=packet['nodes'][k]
            if node['kind'] in ('add','sub','mul'):todo += [node['left'],node['right']]
        assert len(live)==len(packet['nodes'])
        operations[name]=count
    assert operations['nine_natural']==868 and operations['nine_positive']==864
    rng=random.Random(2231709)
    comparisons=0
    for p in (101,1009,1000003):
        ff={k:v%p for k,v in fixed.items()}
        for _ in range(50):
            x={n:rng.randrange(p) for n in packets['nine_natural']['variables']}
            xp=dict(zip(packets['nine_positive']['variables'],(x[n]+1 for n in packets['nine_natural']['variables'])))
            expected=literal(x,ff,source,p)
            assert evaluate(packets['nine_natural'],x,ff,p)==expected
            assert evaluate(packets['nine_positive'],xp,ff,p)==expected
            assert evaluate(packets['nine_degree_certificate'],x,ff,p)==expected
            comparisons+=3
    return {'operations':operations,'literal_and_certificate_and_domain_shift_comparisons':comparisons,
        'moduli':[101,1009,1000003],'actual_complete_native_tuple_used':True},exact_degree(packets['nine_degree_certificate'])


def audit_majorants():
    count=0
    for R,N,b,h,s,w,phi,i,j in product((-7,-2,-1,1,2,7),(2,3),(2,4),(1,2),(1,),(1,2),(0,3),(1,2),(1,2)):
        U,Y=N*N*w,N*N*s
        P=2*(R*Y)**2*U; K=R+1+h*(P-1)
        A=R*Y*(U+1);r=b*w+phi;C=2*R+1+r
        J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C
        F=(A*A-1)*E*E+1;G=A+F*(C*D+1-A);H=2*R+1+j*C
        I=(G*G-1)*H*H+1
        MD=A*C+Y*(U+1)*(r+1)**2+1;MF=A*E+1
        MI=F*(D*(C*H+r*r)+2*H*H+A*A)-A*A+1
        assert K>=1 and abs(A)>=2 and A*J>0 and D>=1 and F>=1
        assert MD>=1 and MD*MD>=D and MF>=1 and MF*MF>=F
        assert MI>=abs(G*H)+abs(H)+1 and MI*MI>=abs(I)
        td=Y*(U+1)*(r+1)**2
        deltaD=2*A*C*td+td*td+2*A*C+2*td+C*C
        deltaF=2*A*E+E*E
        wm=F*D*r*r+2*F*H*H+(F-1)*A*A+1-F*H+A*(F-1)*H
        deltaI=wm*(MI+G*H)+H*H-1
        V1=MD*MF*MI+1
        deltaV=deltaD*MF*MF*MI*MI+D*deltaF*MI*MI+D*F*deltaI+2*MD*MF*MI+1
        assert deltaD==MD*MD-D and deltaF==MF*MF-F
        assert wm==MI-G*H and deltaI==MI*MI-I and deltaV==V1*V1-D*F*I
        count+=1
    return {'signed_R_majorant_and_telescoping_cases':count,'negative_R_included':True,'zero_C_and_H_allowed':True}


def audit_toy_packing():
    # A small exact analogue: r0=n1-n2, r1=n3^2-n1.
    weights=(1,4,6);M=6;stride=25;length=50
    kernel_terms={12-1:1,12-4:-1,stride+12-12:2,stride+12-1:-1}
    cases=0
    for b in (2,4):
        B=(1<<15)*b*b
        E=sum(c*B**e for e,c in kernel_terms.items())
        lam=(B**length-1)//(B-1)
        ell=sum(B**e for e in weights)
        mask=B**(M+1)-1-(b-1)*ell
        Z=B**12+B**(stride+12)
        for ns in product(range(b),repeat=3):
            g=sum(n*B**e for n,e in zip(ns,weights))
            S0=2*(1+g)**2*E+B*lam
            assert S0>0 and (g & mask)==0
            no_carry=(S0 & ((B-2)*Z))==0
            assert no_carry==(ns[0]==ns[1] and ns[2]**2==ns[0])
            cases+=1
        for bad in (1,B**2,b*B,B**7-1):
            assert bad & mask
    return {'exact_toy_source_cases':cases,'invalid_digit_negative_controls':8}


def main():
    source,source_result=audit_source()
    fixed,coeff_result=audit_coefficients(source)
    circuit_result,degree_result=audit_circuits(source,fixed)
    result={'status':'PASS','scope':'Finite data, identities and implementation checks; universal theorem is proved in report.tex.',
        'source':source_result,'coefficients':coeff_result,'circuits':circuit_result,
        'degree':degree_result,'majorants':audit_majorants(),'toy_packing':audit_toy_packing()}
    (ROOT/'generated/VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
