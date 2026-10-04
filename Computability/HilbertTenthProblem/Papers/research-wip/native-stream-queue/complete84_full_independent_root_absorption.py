#!/usr/bin/env python3
"""Fresh inert-source evidence for all91 fixed-polynomial strong-root absorption.
No predecessor is imported/executed; no generic-G circuit or native full zero.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

PINS = {'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737', 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade', 'complete84_signed_quotient_absorption.py': 'cc5ed27ffcffefbd76b85ea36efa05637e06a0eb7fa221c6d9e31af9ea4f9d5f', 'complete84_signed_quotient_absorption.json': 'c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00', 'complete84_signed_quotient_absorption.md': '79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9', 'complete84_strong_root_absorption.py': '3d17fb1bdf7e3942bedcc873ee87a244ef66aa1188eaafb732828965ebfc670c', 'complete84_strong_root_absorption.json': '424ba5aaa6e1ebc8525e4eaaaca7f7489282c7533d775dac86d10a659684986a', 'complete84_strong_root_absorption.md': 'b73fb50aebb8de23a282aff91c389d74b4bd96dadd355c43eb7e7783c1b6abc2', 'complete84_multiplier_dependent_root_absorption.py': '4fbb8595e4956f43829f91e42a57836bc726c3261bc5f9abf0b473d2493e80c4', 'complete84_multiplier_dependent_root_absorption.json': '720c602d9d82d456fd50fb9b5c4f66132e6b4ca1222c9832694ddf0d9b92a46b', 'complete84_multiplier_dependent_root_absorption.md': '045a1147a09d3d70550c9f5c6dcf398d8c9686dbfa957f00d263fb868a485d75', 'review_complete84_multiplier_dependent_root_absorption.md': '743d51a45fbd5d3fe99d182eaf5f22d0d916430ffcd0c75b87c7d4442452d34e'}
SCOUT_PINS = {'complete84_full_f_independent_root_scout.md': 'e1169534645f9f1455cc7d68b03e0e73c0ee63b8581d7010643f59a080e9cd24', 'review_complete84_full_f_independent_root_scout.md': '1c64f6249c28e27472f0f2d8b4bfab808a6b918d5056ab560834c2040cfdd9e4'}
AUX = {'i', 'f', 'auxiliary_quotient', 'y_aux'}
FACTORS = ['norm_first', 'norm_main', 'norm_input', 'norm_index', 'norm_transport']
CUTS = ['A', 'R10a', 'r_lhs'] + FACTORS

def check(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            check(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def reject(value):
        raise ValueError('noninteger JSON ' + value)
    return json.loads(path.read_text(), object_pairs_hook=pairs,
                      parse_float=reject, parse_constant=reject)


def constant(n):
    return {(): n} if n else {}


def var(name):
    return {(name,): 1}


def add(a, b, sign=1):
    result = dict(a)
    for monomial, coefficient in b.items():
        result[monomial] = result.get(monomial, 0) + sign * coefficient
    return {m: c for m, c in result.items() if c}


def multiply(a, b):
    result = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m + n))
            result[key] = result.get(key, 0) + c * d
    return {m: c for m, c in result.items() if c}


def product(*values):
    result = constant(1)
    for value in values:
        result = multiply(result, value)
    return result


def power(value, n):
    return product(*[value for _ in range(n)])


def record(value):
    return [[list(m), c] for m, c in sorted(value.items())]


def symbolic_source(packet):
    rows = packet['source']
    dependencies = {name: {name} for name in packet['free']}
    known = set(dependencies)
    definitions = {}
    for row in rows:
        check(type(row) is list and len(row) == 4, 'binary source row')
        name, op, a, b = row
        check(type(name) is str and name not in known and op in ['+', '-', '*'], 'SSA/opcode')
        check(all(type(v) is int or type(v) is str and v in known for v in [a, b]), 'source topology')
        dependencies[name] = set().union(*(dependencies[v] for v in [a, b] if type(v) is str))
        known.add(name)
        definitions[name] = row
    outside = [row[0] for row in rows if not dependencies[row[0]] & AUX]
    supplied = [name for name in packet['free'] if name not in AUX]
    check(len(outside) == 64 and len(supplied) == 21, 'full85 exterior census')
    check(set(CUTS) <= set(outside), 'actual auxiliary-independent cuts')
    check([r for r in rows if 'f' in r[2:]] == [
        ['L16', '*', 'f', 'f'],
        ['auxiliary_Tf', '*', 'auxiliary_quotient', 'f']], 'sole two f consumers')
    check([r for r in rows if 'auxiliary_quotient' in r[2:]] == [
        ['auxiliary_Tf', '*', 'auxiliary_quotient', 'f']], 'sole quotient consumer')
    for row in [
        ['R12', '+', 'UM', 'sn2'], ['UM', '*', 'wn2', 'sn2'],
        ['a_square', '*', 'R12', 'R12'], ['a4', '*', 4, 'R12'],
        ['a4m5', '+', 'a4', 3], ['A', '+', 'a_square', 'a4m5']]:
        check(definitions[row[0]] == row, 'positive discriminant boundary')
    expanded = set()
    def run(f_value, quotient_value):
        memo = {name: var(name) for name in packet['free'] + CUTS}
        memo['f'], memo['auxiliary_quotient'] = f_value, quotient_value
        def at(name):
            if type(name) is int:
                return constant(name)
            if name not in memo:
                _, op, a, b = definitions[name]
                a, b = at(a), at(b)
                memo[name] = multiply(a, b) if op == '*' else add(a, b, 1 if op == '+' else -1)
                expanded.add(name)
            return memo[name]
        return at(packet['output'])
    D, c, R, i, f, T, y = [var(n) for n in ['A', 'R10a', 'r_lhs', 'i', 'f', 'auxiliary_quotient', 'y_aux']]
    P5 = product(*(var(n) for n in FACTORS))
    Q = power(product(D, i, c, c), 2)
    V = add(product(c, add(product(T, f), constant(1), -1)), product(R, f, f), -1)
    Na = add(product(Q, add(power(V, 2), power(y, 2), -1)), power(y, 2))
    Ns = add(product(D, f, f), Q, -1)
    expected = add(product(P5, Na, Ns), D, -1)
    full = run(f, T)
    check(full == expected, 'full actual-source polynomial factor identity')
    check(run(product(constant(-1), f), product(constant(-1), T)) == full,
          'full simultaneous sign reversal')
    at_zero = run({}, T)
    zero_na = add(product(Q, add(power(c, 2), power(y, 2), -1)), power(y, 2))
    zero_formula = product(constant(-1), D,
        add(product(D, i, i, c, c, c, c, P5, zero_na), constant(1)))
    check(at_zero == zero_formula, 'full zero-f contraction')
    check(all('auxiliary_quotient' not in m for m in at_zero), 'quotient disappears at zero root')
    return dict(computed_exterior=outside, supplied_exterior=supplied,
        exact_cut_names=CUTS, expanded_output_ancestors=[r for r in rows if r[0] in expanded],
        full_coefficients=record(full), zero_f_coefficients=record(at_zero),
        full_sign_identity=True, full_zero_root_identity=True)


def extended_interface(packet, old):
    removed = {'f', 'auxiliary_quotient', 'y_aux'}
    dependencies = {name: {name} for name in packet['free']}
    rows = packet['source']
    definitions = {r[0]: r for r in rows}
    for name, op, a, b in rows:
        dependencies[name] = set().union(*(dependencies[v] for v in [a, b] if type(v) is str))
    computed = [r[0] for r in rows if not dependencies[r[0]] & removed]
    supplied = [n for n in packet['free'] if n not in removed]
    check(len(computed) == 66 and len(supplied) == 22, 'exact88 literal boundary')
    check(set(computed) - set(old['computed_exterior']) == {'aux_coefficient_root', 'R16'}, 'only two added computed values')
    check(set(supplied) - set(old['supplied_exterior']) == {'i'}, 'only one added supplied value')
    for row in [
        ['c2', '*', 'R10a', 'R10a'], ['Ac2', '*', 'A', 'c2'],
        ['aux_coefficient_root', '*', 'i', 'Ac2'],
        ['R16', '*', 'aux_coefficient_root', 'aux_coefficient_root'],
        ['scaled_f_square', '*', 'A', 'L16'],
        ['norm_strong', '-', 'scaled_f_square', 'R16']]:
        check(definitions[row[0]] == row, 'literal multiplier/strong boundary')
    old_names = old['computed_exterior'] + old['supplied_exterior']
    memo = {n: var(n) for n in old_names}
    memo['i'] = var('z')
    # Re-expand the real c² and Delta*c² producers rather than leave them as
    # independent coefficient ports: this proves the coefficient weights used.
    memo['c2'] = power(var('R10a'), 2)
    memo['Ac2'] = product(var('A'), memo['c2'])
    def at(n):
        if type(n) is int:
            return constant(n)
        if n not in memo:
            _, op, a, b = definitions[n]
            a, b = at(a), at(b)
            memo[n] = multiply(a, b) if op == '*' else add(a, b, 1 if op == '+' else -1)
        return memo[n]
    S = at('aux_coefficient_root')
    Q = at('R16')
    check(S == product(var('A'), power(var('R10a'), 2), var('z')), 'actual S specialization')
    check(Q == product(power(var('A'), 2), power(var('R10a'), 4), power(var('z'), 2)), 'actual S² specialization')
    weights = [{ 'name': n, 'coefficient_c_exponent': 4, 'z_degree': 0 } for n in old_names]
    weights += [dict(name='i', coefficient_c_exponent=0, z_degree=1),
                dict(name='aux_coefficient_root', coefficient_c_exponent=3, z_degree=1),
                dict(name='R16', coefficient_c_exponent=6, z_degree=2)]
    check({x['name'] for x in weights} == set(computed + supplied) and len(weights) == 88, 'one weight for every actual argument')
    check(all(not dependencies[n] & removed for n in computed + supplied), 'sign map fixes all88 arguments')
    return dict(computed=computed, supplied=supplied,
        excluded_computed=[r[0] for r in rows if r[0] not in computed],
        added_computed=[definitions[n] for n in ['aux_coefficient_root', 'R16']],
        multiplier_polynomials=dict(S=record(S), S_squared=record(Q)),
        pointwise_argument_weights=weights)



def substitute(p, bindings):
    result = {}
    for monomial, coeff in p.items():
        result = add(result, product(constant(coeff), *(bindings.get(n, var(n)) for n in monomial)))
    return result


def norm(p):
    return sum(abs(v) for v in p.values())


def coefficient(p, name, degree):
    return {tuple(v for v in m if v != name): c for m, c in p.items() if m.count(name) == degree}


def determinant(matrix):
    # Division-free determinant, used only for bounded formal diagnostics.
    n = len(matrix)
    check(all(len(row) == n for row in matrix), 'square matrix')
    memo = {0: constant(1)}
    for row in range(n):
        nxt = {}
        for mask, value in memo.items():
            for col in range(n):
                if not mask & (1 << col):
                    sign = -1 if (mask >> (col + 1)).bit_count() % 2 else 1
                    key = mask | (1 << col)
                    nxt[key] = add(nxt.get(key, {}), multiply(value, matrix[row][col]), sign)
        memo = nxt
    return memo[(1 << n) - 1]


def resultant_y(c, h):
    check(c and max(m.count('y') for m in c) == 2, 'quadratic conic')
    if not h:
        return {}
    m = max(mon.count('y') for mon in h)
    if m == 0:
        return power(h, 2)
    cc = [coefficient(c, 'y', j) for j in range(2, -1, -1)]
    hh = [coefficient(h, 'y', j) for j in range(m, -1, -1)]
    matrix = [[{} for _ in range(m+2)] for _ in range(m+2)]
    for row in range(m):
        matrix[row][row:row+3] = cc
    for row in range(2):
        matrix[m+row][row:row+m+1] = hh
    return determinant(matrix)


def source91(packet, old, ext, signed):
    definitions = {r[0]: r for r in packet['source']}
    deps = {n: {n} for n in packet['free']}
    for name, op, a, b in packet['source']:
        deps[name] = set().union(*(deps[n] for n in [a, b] if type(n) is str))
    computed = [r[0] for r in packet['source'] if 'f' not in deps[r[0]]]
    supplied = [n for n in packet['free'] if n != 'f']
    check(len(computed) == 67 and len(supplied) == 24, 'actual full91 census')
    check(set(computed)-set(ext['computed']) == {'aux_y2'}, 'sole added computed port')
    check(set(supplied)-set(ext['supplied']) == {'auxiliary_quotient', 'y_aux'}, 'two added supplied ports')
    check(definitions['aux_y2'] == ['aux_y2', '*', 'y_aux', 'y_aux'], 'actual y square')
    check(set(ext['computed']+ext['supplied']) <= set(signed['census']['new_computed']+signed['census']['new_free']), 'E88 inside signed bounded93')
    live = {packet['output']}
    for name, op, a, b in reversed(packet['source']):
        if name in live:
            live.update(n for n in [a,b] if type(n) is str)
    check(set(definitions) | set(packet['free']) <= live, 'all parent rows and ports live')
    check(sum(r[1]=='*' for r in packet['source']) == 47 and len(packet['source']) == 84, 'unchanged84=47M37A')
    memo = {n: var(n) for n in packet['free']+CUTS}
    def at(n):
        if type(n) is int: return constant(n)
        if n not in memo:
            _, op, a, b = definitions[n]
            memo[n] = multiply(at(a),at(b)) if op=='*' else add(at(a),at(b),1 if op=='+' else -1)
        return memo[n]
    D,c,R,i,f,T,y = [var(n) for n in ['A','R10a','r_lhs','i','f','auxiliary_quotient','y_aux']]
    S = product(D,i,c,c); Q=power(S,2)
    b = add(c,product(R,f,f)); V=add(product(c,f,T),b,-1)
    C=add(add(product(Q,power(V,2)),product(add(Q,constant(1),-1),power(y,2)),-1),constant(1),-1)
    check(at('aux_u_rhs') == V and at('R16') == Q, 'actual V and Q binding')
    check(add(at('norm_aux'),constant(1),-1) == C, 'actual auxiliary unit is conic C=0')
    strong = add(power(f,2),product(D,i,i,c,c,c,c),-1)
    check(at('norm_strong') == multiply(D,strong), 'actual normalized strong factor')
    check(old['computed_exterior'] == signed['census']['old_computed'] and old['supplied_exterior'] == signed['census']['old_free'], 'actual old85 bound interface')
    return dict(computed=computed,supplied=supplied,total=91,
        added_from88=[definitions['aux_y2'],'auxiliary_quotient','y_aux'],
        dependency_rows=[dict(name=n,free_dependencies=sorted(deps[n])) for n in computed+supplied],
        all_source_and_free_live=True,ledger=dict(M=47,A=37,total=84),
        actual_V=record(V),actual_Q=record(Q),actual_conic=record(C),
        actual_normalized_strong=record(strong),native_bound_ports=ext['computed']+ext['supplied'])


def formal_evidence():
    Q,c,f,b,T,y=[var(n) for n in ['Q','c','f','b','T','y']]
    cf=product(c,f)
    C=add(add(product(Q,power(add(product(cf,T),b,-1),2)),product(add(Q,constant(1),-1),power(y,2)),-1),constant(1),-1)
    matrix=[[product(Q,power(cf,2)),{},product(constant(-1),Q,cf,b)],
            [{},add(constant(1),Q,-1),{}],
            [product(constant(-1),Q,cf,b),{},add(product(Q,power(b,2)),constant(1),-1)]]
    det=determinant(matrix)
    check(det==product(Q,add(Q,constant(1),-1),power(cf,2)), 'rank3 projective conic determinant')
    discr=add(power(product(constant(-2),Q,cf,b),2),product(constant(4),Q,power(cf,2),add(product(Q,power(b,2)),constant(1),-1)),-1)
    check(discr==product(constant(4),Q,power(cf,2)), 'two distinct T roots of radicand')
    num,den=var('num'),var('den'); divisor=add(product(den,y,y),num,-1)
    remainders=[]
    for d in range(1,7):
        for j in range(2*d+1):
            k,e=divmod(j,2)
            lhs=add(product(power(den,d),power(y,j)),product(power(num,k),power(den,d-k),power(y,e)),-1)
            quotient={}
            for r in range(k):
                quotient=add(quotient,product(power(den,d-k),power(y,e),power(product(den,y,y),k-1-r),power(num,r)))
            check(lhs==multiply(divisor,quotient),'cleared even/odd remainder identity')
            remainders.append([d,j,k,e,len(quotient)])
    signs=[]
    for s in [-1,1]:
        for e in range(5):
            for t in range(5-e):
                for a in range(5-e-t):
                    for z in range(5-e-t-a):
                        mon=product(power(var('E'),e),power(var('T'),t),power(var('y'),a),power(var('y2'),z))
                        gs=product(constant(s),substitute(mon,{'T':product(constant(s),var('T'))}))
                        restored=substitute(gs,{'T':product(constant(s),var('T')),'y2':power(var('y'),2)})
                        check(restored==product(constant(s),substitute(mon,{'y2':power(var('y'),2)})),'signed G with actual y-square')
                        check(norm(gs)==norm(mon),'sign preserves formal coefficient norm')
                        signs.append([s,e,t,a,z])
    z,A=var('z'),var('A')
    strong_quadratic=add(constant(1),product(A,power(z,2)))
    # Discriminant -4A is nonzero for A=Delta*c^4>0; this is the
    # squarefree polynomial used by the rational-function nonsquare proof.
    check(add({},product(constant(4),A),-1)==product(constant(-4),A),'strong quadratic discriminant')
    return dict(conic=record(C),projective_determinant=record(det),radicand_discriminant=record(discr),
        denominator_clearing_cases=remainders,signed_monomial_cases=signs,
        rational_nonsquare_base=record(strong_quadratic),rational_nonsquare_discriminant=record(product(constant(-4),A)))


def diagnostics():
    resultants=[]
    T,y=var('T'),var('y')
    for Q,c,f,b in [(4,1,2,3),(9,2,2,7),(16,1,3,2)]:
        C=add(add(product(constant(Q),power(add(product(constant(c*f),T),constant(b),-1),2)),product(constant(Q-1),power(y,2)),-1),constant(1),-1)
        cases=[('one',constant(1),constant(1)),
               ('no_y',add(T,constant(1),-1),power(add(T,constant(1),-1),2)),
               ('linear_y',add(y,constant(1),-1),substitute(C,{'y':constant(1)})),
               ('multiple',multiply(C,add(T,y)),{}),
               ('degree_drop',product(add(T,constant(1),-1),add(y,constant(2))),product(power(add(T,constant(1),-1),2),substitute(C,{'y':constant(-2)}))),
               ('zero',{}, {})]
        for label,H,expected in cases:
            P=resultant_y(C,H)
            check(P==expected,'bounded exact resultant '+label)
            resultants.append(dict(parameters=[Q,c,f,b],case=label,H=record(H),resultant=record(P)))
    norm_cases=[]
    for f in [2,3,4]:
        Q,c,R=f**3,f**3,f**3
        b=c+R*f*f
        C=add(add(product(constant(Q),power(add(product(constant(c*f),T),constant(b),-1),2)),product(constant(Q-1),power(y,2)),-1),constant(1),-1)
        check(norm(C)<=20*f**13,'conic coefficient norm')
        for d in [1,2,3]:
            H=add(add(power(y,2*d),product(constant(2),T)),constant(-f))
            L=3; m=2*d;P=resultant_y(C,H)
            K=math.factorial(2*d+2)*20**(2*d)*(L+1)**2
            check(norm(H)<=(L+1)*f**(3*d) and norm(P)<=K*f**(32*d),'Sylvester coefficient norm')
            norm_cases.append(dict(f=f,d=d,m=m,L=L,conic_norm=norm(C),H_norm=norm(H),resultant_norm=norm(P),K=K))
    cutoffs=[]
    for d in range(1,5):
        for L in [1,2,7,16]:
            K=math.factorial(2*d+2)*20**(2*d)*(L+1)**2
            bound=32*d+4+K.bit_length() # ceil(log2(K+1))
            for f in [2,3]:
                check(f**(bound-4)>=(K+1)*f**(32*d),'nonzero resultant cutoff endpoint')
            cutoffs.append(dict(branch='nonzero_resultant',d=d,L=L,K=K,R_strict_bound=bound))
    for t in range(1,5):
        for LA,LB in [(0,1),(1,1),(3,2),(16,7)]:
            K=LA*LA+2*LB*LB+1; exponent=12*t+8
            cutoff=exponent+1+(K-1).bit_length()
            for c in [cutoff,cutoff+1]:
                check(c**(c-1)>=K*c**exponent,'rational88 cutoff endpoint')
            cutoffs.append(dict(branch='zero_resultant',t=t,LA=LA,LB=LB,K=K,c_strict_bound=cutoff))
    return dict(exact_resultant_cases=resultants,norm_cases=norm_cases,cutoff_cases=cutoffs,
        scope='Bounded formal algebra and coefficient estimates only. No full native zeros, histories, or execution of predecessor evidence.')


def build(root):
    for n,h in PINS.items(): check(sha((root/n).read_bytes())==h,'dependency pin '+n)
    packet=read(root/'complete84_scaled_strong_output.json')['packet']
    original_packet=canonical(packet)
    signed=read(root/'complete84_signed_quotient_absorption.json')
    strong=read(root/'complete84_strong_root_absorption.json')
    multi=read(root/'complete84_multiplier_dependent_root_absorption.json')
    check(signed['authenticated_parent_source']==strong['authenticated_source']==multi['authenticated_source']==packet['source'],'identical inherited full84 source')
    for stem,receipt in [('complete84_signed_quotient_absorption',signed),('complete84_strong_root_absorption',strong),('complete84_multiplier_dependent_root_absorption',multi)]:
        check(receipt['source_sha256']==PINS[stem+'.py'],'inherited source-byte binding')
    check(signed['theorem']['normalized_rank']=='c=psi_p(A0), f=chi_m(A0), psi_m(A0)=i*c^2, p*c divides m, p=R','signed normalized rank premise')
    check(signed['theorem']['all93_bound']=='absolute values <=f^3' and not signed['theorem']['positive_T_parent_restoration_used'],'direct signed bounds')
    check(multi['theorem']['lower_bound']=='i>c^(c-1)','all-completion multiplier growth')
    old=symbolic_source(packet);ext=extended_interface(packet,old)
    check(ext['computed']==multi['extended_interface']['computed'] and ext['supplied']==multi['extended_interface']['supplied'],'same exact88 interface')
    census=source91(packet,old,ext,signed)
    check(canonical(packet)==original_packet,'parent packet remains immutable')
    return dict(status='PASS_FULL91_ROOT_ABSORPTION',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,authoring_provenance=SCOUT_PINS,
        authenticated_source=packet['source'],authenticated_free=packet['free'],authenticated_output=packet['output'],parent_packet_immutable=True,
        full_source_evidence=old,interface88=ext,interface91=census,formal_evidence=formal_evidence(),diagnostics=diagnostics(),
        theorem=dict(domain='Fixed integer polynomial f=G on all91 literal f-independent source values; every other original supplied witness remains positive on a valid fixed compiler slice',
            zero_G_sector='empty before decoding',restoration='s=sign(G), f_new=abs(G), T_new=s*T_old; G_s(E,T,y,y2)=s*G(E,s*T,y,y2)',
            conic='Q*(c*f*T-c-R*f^2)^2-(Q-1)*y^2-1=0',d='max(1,degree(G))',L='max(1,l1(G))',
            resultant_bound='K=(2d+2)!*20^(2d)*(L+1)^2; nonzero specialized P has l1(P)<=K*f^(32d)',
            nonzero_resultant_cutoff='u<R<32d+4+ceil(log2(K+1))',
            zero_resultant_map='B(E)=(Q-1)^d>0; A(E) is the cleared even remainder at T=0; f=A/B',
            rational_norms='t=max(deg(A),deg(B),1); LA=l1(A), LB=l1(B); zero A may be assigned degree0',
            zero_resultant_cutoff='u<R<c<12t+9+ceil(log2(LA^2+2LB^2+1))',
            projection='Finite whole ordinary-input projection for each fixed G; take maximum of two sign bounds and the nonzero-resultant bound'),
        scope=dict(predecessor_execution=False,predecessor_import=False,new_circuit=False,generic_G_compiler=False,
            full_native_zero_fixtures=False,new_gate_bound=False,signed_full_compiler_transfer=False))


def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=p.parse_args();receipt=build(a.root)
    if a.output:
        with a.output.open('x') as f:f.write(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    else:check(canonical(receipt)==canonical(read(a.expect)),'exact type-sensitive receipt replay')
    print(receipt['status'],'actual67+24 interface; unchanged84 source; both specialized-resultant branches')


if __name__=='__main__':main()
