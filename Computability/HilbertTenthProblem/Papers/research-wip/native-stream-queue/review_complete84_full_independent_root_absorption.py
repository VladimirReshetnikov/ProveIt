"""Fresh independent review. All author/predecessor files are inert input bytes."""
import argparse
import hashlib
import itertools
import json
from math import factorial
from pathlib import Path

AUTHOR = {
 'complete84_full_independent_root_absorption.py': '02698613d648ab7db6a707471aed6346540725aa64bfe426f7b5d3dd36d16776',
 'complete84_full_independent_root_absorption.json': '4b0eac23c21a9cf7cf177cd19fface8cccff2a1a8dc0cbc70d6af16fca115320',
 'complete84_full_independent_root_absorption.md': '1280fb32702c4ec99f69807ee4b6fd0bdbd5f83830e5187c41bfbc81da7935b7',
}
SOURCE_SHA = '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
PROOFS = {
 'complete84_multiplier_dependent_root_absorption.md': '045a1147a09d3d70550c9f5c6dcf398d8c9686dbfa957f00d263fb868a485d75',
 'complete84_signed_quotient_absorption.md': '79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9',
 'complete84_strong_root_absorption.md': 'b73fb50aebb8de23a282aff91c389d74b4bd96dadd355c43eb7e7783c1b6abc2',
}

def check(ok, why):
    if not ok:
        raise ValueError(why)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':')).encode()

def read_json(path):
    def pairs(xs):
        out = {}
        for k, v in xs:
            check(k not in out, 'duplicate JSON key')
            out[k] = v
        return out
    def bad(x):
        raise ValueError('noninteger JSON number '+x)
    return json.loads(path.read_bytes(), object_pairs_hook=pairs, parse_float=bad, parse_constant=bad)

# Commutative sparse polynomials in explicitly named formal cuts.
def num(n):
    return {(): n} if n else {}

def var(n):
    return {(n,): 1}

def plus(a, b, s=1):
    c = dict(a)
    for m, n in b.items():
        c[m] = c.get(m, 0)+s*n
    return {m: n for m, n in c.items() if n}

def times(a, b):
    c = {}
    for m, n in a.items():
        for v, w in b.items():
            k = tuple(sorted(m+v))
            c[k] = c.get(k, 0)+n*w
    return {m: n for m, n in c.items() if n}

def prod(*xs):
    p = num(1)
    for x in xs:
        p = times(p, x)
    return p

def power(p, n):
    return prod(*([p]*n))

def serial(p):
    return [[list(m), c] for m, c in sorted(p.items())]

def substitute(p, values):
    out = {}
    for m, c in p.items():
        out = plus(out, prod(num(c), *(values.get(v, var(v)) for v in m)))
    return out

def norm(p):
    return sum(abs(x) for x in p.values())

def coefficients(p, v):
    out = {}
    for m, c in p.items():
        e = m.count(v)
        r = tuple(x for x in m if x != v)
        out[e] = plus(out.get(e, {}), {r: c})
    return {e: c for e, c in out.items() if c}

def determinant(rows):
    n = len(rows)
    ans = {}
    for perm in itertools.permutations(range(n)):
        sign = -1 if sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n)) % 2 else 1
        ans = plus(ans, prod(num(sign), *(rows[i][perm[i]] for i in range(n))))
    return ans

def resultant_y(a, b):
    aa, bb = coefficients(a, 'y'), coefficients(b, 'y')
    if not bb:
        return {}
    n, m = max(aa), max(bb)
    if m == 0:
        return power(bb[0], n)
    av, bv = [aa.get(i, {}) for i in range(n, -1, -1)], [bb.get(i, {}) for i in range(m, -1, -1)]
    rows = []
    for coeff, count in [(av, m), (bv, n)]:
        for shift in range(count):
            rows.append([{}]*shift+coeff+[{}]*(n+m-shift-len(coeff)))
    return determinant(rows)

def source_checks(p):
    rows, free = p['source'], p['free']
    check(len(rows) == 84 and len(free) == len(set(free)) == 25, 'literal source size')
    check(sum(r[1] == '*' for r in rows) == 47, '47M37A')
    deps = {n: {n} for n in free}; definitions = {}
    for row in rows:
        check(type(row) is list and len(row) == 4, 'literal row shape')
        n, op, a, b = row
        check(n not in deps and op in ('*', '+', '-'), 'SSA/operator')
        check(all(type(v) is int or type(v) is str and v in deps for v in (a, b)), 'topology')
        definitions[n] = row
        deps[n] = set().union(*(deps[v] for v in (a, b) if type(v) is str))
    live = set()
    def visit(n):
        if type(n) is int or n in live:
            return
        live.add(n)
        if n in definitions:
            visit(definitions[n][2]); visit(definitions[n][3])
    visit(p['output']); check(live == set(deps), 'all source/free nodes live')
    census = {}
    for tag, blocked, counts in [('old85', {'f','i','auxiliary_quotient','y_aux'}, (64,21)),
                                 ('E88', {'f','auxiliary_quotient','y_aux'}, (66,22)),
                                 ('all91', {'f'}, (67,24))]:
        computed = [r[0] for r in rows if not deps[r[0]] & blocked]
        supplied = [n for n in free if n not in blocked]
        check((len(computed), len(supplied)) == counts, 'exact '+tag+' census')
        census[tag] = {'computed': computed, 'supplied': supplied}
    check(set(census['all91']['computed'])-set(census['E88']['computed']) == {'aux_y2'}, 'one computed extension')
    check(set(census['all91']['supplied'])-set(census['E88']['supplied']) == {'auxiliary_quotient','y_aux'}, 'two supplied extensions')
    check([r for r in rows if 'f' in r[2:]] == [['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']], 'all direct f consumers')
    check([r for r in rows if 'auxiliary_quotient' in r[2:]] == [['auxiliary_Tf','*','auxiliary_quotient','f']], 'all direct T consumers')
    factors = ['norm_first','norm_main','norm_input','norm_index','norm_transport']
    cutmap = dict(zip(['A','R10a','r_lhs']+factors, ['Delta','c','R']+factors))
    check(set(cutmap) <= set(census['old85']['computed']), 'cuts independent of all auxiliary witnesses')
    reached = set()
    def evaluate(sign=1, zero=False):
        env = {n: var(n) for n in free}
        env.update({n: var(v) for n,v in cutmap.items()})
        env['f'] = {} if zero else prod(num(sign), var('f'))
        env['auxiliary_quotient'] = prod(num(sign), var('T'))
        env['y_aux'] = var('y')
        def at(n):
            if type(n) is int:
                return num(n)
            if n not in env:
                reached.add(n)
                _, op, a, b = definitions[n]
                aa, bb = at(a), at(b)
                env[n] = times(aa, bb) if op == '*' else plus(aa, bb, 1 if op == '+' else -1)
            return env[n]
        return at, env
    at, env = evaluate(); out = at(p['output'])
    Delta,c,R,f,i,T,y = [var(n) for n in ['Delta','c','R','f','i','T','y']]
    S = prod(Delta,i,power(c,2)); Q = power(S,2)
    V = plus(plus(prod(c,T,f), c, -1), prod(R,power(f,2)), -1)
    Na = plus(prod(Q,plus(power(V,2),power(y,2),-1)),power(y,2))
    Ns = plus(prod(Delta,power(f,2)),Q,-1)
    P5 = prod(*(var(n) for n in factors))
    check(at('aux_coefficient_root') == S and at('R16') == Q, 'actual S/S2 producers with c2/Ac2 expanded')
    check(at('aux_u_rhs') == V and at('norm_aux') == Na and at('norm_strong') == Ns, 'actual auxiliary factors')
    check(out == plus(prod(P5,Na,Ns),Delta,-1), 'literal whole finalizer')
    check(evaluate(-1)[0](p['output']) == out, 'whole-source simultaneous f/T sign identity')
    zero = evaluate(1,True)[0](p['output'])
    Na0 = plus(prod(Q,plus(power(c,2),power(y,2),-1)),power(y,2))
    bracket = plus(prod(P5,Delta,power(i,2),power(c,4),Na0),num(1))
    check(zero == prod(num(-1),Delta,bracket), 'noncircular whole-source zero-f contraction')
    check(substitute(bracket, {'Delta':num(0)}) == num(1), 'zero bracket is1 moduloDelta')
    check(len(out) == 17 and len(zero) == 4 and len(reached) == 24, 'whole cut expansion sizes')
    weights = [[n,4,0] for n in census['old85']['computed']+census['old85']['supplied']]
    weights += [['i',0,1],['aux_coefficient_root',3,1],['R16',6,2]]
    check(set(w[0] for w in weights) == set(census['E88']['computed']+census['E88']['supplied']), 'all88 coefficient weights')
    return dict(source=rows, free=free, census=census, dependencies={n:sorted(v) for n,v in deps.items()}, excluded_f_dependent=[r for r in rows if 'f' in deps[r[0]]],
                cutmap=cutmap, expanded_ancestors=[r for r in rows if r[0] in reached],
                source_polynomial=serial(out), zero_f=serial(zero), zero_bracket=serial(bracket),
                S=serial(S), Q=serial(Q), V=serial(V), Na=serial(Na), Ns=serial(Ns), rational88_weights=weights)

def mathematical_checks():
    Q,c,f,R,T,y,b = [var(n) for n in ['Q','c','f','R','T','y','b']]
    C = plus(plus(prod(Q,power(plus(prod(c,f,T),b,-1),2)),prod(plus(Q,num(1),-1),power(y,2)),-1),num(1),-1)
    # Determinant of the homogeneous ternary quadratic coefficient matrix.
    aa=prod(Q,power(c,2),power(f,2)); cross=prod(num(-1),Q,c,f,b)
    matrix=[[aa,{},cross],[{},plus(num(1),Q,-1),{}],[cross,{},plus(prod(Q,power(b,2)),num(1),-1)]]
    det=determinant(matrix)
    check(det == prod(Q,plus(Q,num(1),-1),power(c,2),power(f,2)), 'formal nondegenerate conic')
    # Clear a generic monomial remainder y^j with denominator (Q-1)^d.
    N,D = var('N'),var('D'); remainders=[]
    for d in range(1,9):
        for j in range(2*d+1):
            k=j//2
            lhs=prod(power(D,d),power(y,j)); rem=prod(power(N,k),power(D,d-k),power(y,j%2))
            quotient={}
            for h in range(k):
                quotient=plus(quotient,prod(power(D,d-h-1),power(N,h),power(y,j-2*h-2)))
            check(plus(lhs,rem,-1) == prod(plus(prod(D,power(y,2)),N,-1),quotient), 'all monomial even/odd cleared remainders')
            remainders.append([d,j,serial(rem)])
    # Independent Sylvester determinants, not sampled evaluations of a claimed resultant.
    results=[]
    for qv,cv,fv,rv in itertools.product([2,5],[2,3],[2,3],[1,2]):
        bv=cv+rv*fv*fv
        conic=substitute(C, {'Q':num(qv),'c':num(cv),'f':num(fv),'b':num(bv)})
        check(norm(conic)<=20*fv**13, 'conic norm in bounded components')
        for v in [1,2]:
            linear=plus(y,num(v),-1)
            square=plus(power(y,2),num(v*v),-1)
            ev=substitute(conic,{'y':num(v)})
            check(resultant_y(conic,linear)==ev, 'linear resultant')
            check(resultant_y(conic,square)==power(ev,2), 'quadratic resultant')
            results.append([qv,cv,fv,rv,v,serial(ev)])
        h0=plus(T,num(3),-1)
        check(resultant_y(conic,h0)==power(h0,2), 'actual y-degree zero case')
        for mult in [num(1), y, plus(T,y)]:
            check(resultant_y(conic,times(conic,mult))=={}, 'zero resultant divisibility components')
    # Distinct roots of1+Kz2: 2D-zD'=2; K!=0 gives a genuine quadratic.
    z,K=var('z'),var('K'); Dstrong=plus(num(1),prod(K,power(z,2)))
    check(plus(prod(num(2),Dstrong),prod(z,num(2),K,z),-1)==num(2), 'squarefree quadratic Bezout identity')
    js=[]
    choices=[{},num(1),plus(z,num(1)),plus(power(z,2),num(-2)),plus(prod(num(2),z),num(3))]
    for kval in [1,2,3,8,15,16,24]:
        for a in choices:
            for bb in choices[1:]:
                J=plus(power(a,2),prod(substitute(Dstrong,{'K':num(kval)}),power(bb,2)),-1)
                check(bool(J), 'rational-square finite nonzero corroboration')
                js.append([kval,serial(a),serial(bb),serial(J)])
    ceilings=[]
    for d in range(1,7):
        for L in [1,2,3,8,17]:
            bound=factorial(2*d+2)*20**(2*d)*(L+1)**2
            k=(bound).bit_length() # ceil(log2(bound+1))
            threshold=32*d+4+k
            check(2**(threshold-4-32*d)>=bound+1, 'resultant cutoff at boundary')
            for m in range(2*d+1):
                check(13*m+6*d<=32*d and factorial(m+2)*20**m<=factorial(2*d+2)*20**(2*d), 'Sylvester norm exponent/constant')
            ceilings.append([d,L,bound,threshold])
    rational=[]
    for t,La,Lb in itertools.product(range(1,7),[0,1,2,7],[1,2,5]):
        k=La*La+2*Lb*Lb+1; e=12*t+8; s=(k-1).bit_length(); bound=e+1+s
        check(bound**(bound-1-e)>=k, 'rational88 cutoff at boundary')
        rational.append([t,La,Lb,k,bound])
    return dict(conic=serial(C), homogeneous_determinant=serial(det), cleared_remainders=remainders,
                resultant_components=results, rational_nonzero_components=js,
                resultant_cutoffs=ceilings, rational88_cutoffs=rational,
                scope='Finite formal/arithmetic corroboration only; no source zero, compiled history, generic G compiler or full quantified decision procedure.')

def from_records(rows):
    result = {}
    for m,c in rows:
        check(type(m) is list and type(c) is int and c != 0 and tuple(m) not in result, 'coefficient record')
        result[tuple(m)] = c
    return result

def author_checks(saved, own, formal, root):
    for n,h in saved['pins'].items():
        check(sha((root/n).read_bytes()) == h, 'author dependency bytes '+n)
    check(saved['source_sha256'] == AUTHOR['complete84_full_independent_root_absorption.py'], 'author self binding')
    check(saved['authenticated_source'] == own['source'] and saved['authenticated_free'] == own['free'] and saved['authenticated_output'] == 'polynomial', 'all84/25 actual author source fields')
    for tag, key in [('E88','interface88'),('all91','interface91')]:
        for part in ['computed','supplied']:
            check(saved[key][part] == own['census'][tag][part], 'author exact '+tag+' '+part)
    check(saved['interface91']['native_bound_ports'] == own['census']['E88']['computed']+own['census']['E88']['supplied'], 'only88 ports receive the f3 bound')
    names=own['census']['all91']['computed']+own['census']['all91']['supplied']
    check(saved['interface91']['dependency_rows'] == [dict(name=n,free_dependencies=own['dependencies'][n]) for n in names], 'all91 author closure certificates')
    check(saved['parent_packet_immutable'] is True, 'author parent immutability flag')
    old=saved['full_source_evidence']
    check(old['computed_exterior']==own['census']['old85']['computed'] and old['supplied_exterior']==own['census']['old85']['supplied'], 'old85 interface')
    check(old['expanded_output_ancestors']==own['expanded_ancestors'] and old['exact_cut_names']==list(own['cutmap']), 'all24 expanded ancestors/eight real cuts')
    rename={'A':var('Delta'),'R10a':var('c'),'r_lhs':var('R'),'auxiliary_quotient':var('T'),'y_aux':var('y')}
    def translate(rows):
        return substitute(from_records(rows),rename)
    for field, ownfield in [('full_coefficients','source_polynomial'),('zero_f_coefficients','zero_f')]:
        check(translate(old[field])==from_records(own[ownfield]), 'whole coefficient equality '+field)
    ownNa=from_records(own['Na'])
    targets={'actual_V':from_records(own['V']),'actual_Q':from_records(own['Q']),
             'actual_conic':plus(ownNa,num(1),-1),
             'actual_normalized_strong':plus(power(var('f'),2),prod(var('Delta'),power(var('i'),2),power(var('c'),4)),-1)}
    for key, expected in targets.items():
        check(translate(saved['interface91'][key])==expected,'exact actual source binding '+key)
    check([[w['name'],w['coefficient_c_exponent'],w['z_degree']] for w in saved['interface88']['pointwise_argument_weights']]==own['rational88_weights'],'all88 rational coefficient weights')
    af=saved['formal_evidence']
    check(af['conic']==formal['conic'] and af['projective_determinant']==formal['homogeneous_determinant'],'formal conic and rank determinant')
    check(from_records(af['radicand_discriminant'])==prod(num(4),var('Q'),power(var('c'),2),power(var('f'),2)),'author radicand discriminant')
    check(from_records(af['rational_nonsquare_base'])==plus(num(1),prod(var('A'),power(var('z'),2))) and from_records(af['rational_nonsquare_discriminant'])==prod(num(-4),var('A')),'rational squarefree base')
    expected_remainders=[[d,j,j//2,j%2,j//2] for d in range(1,7) for j in range(2*d+1)]
    check(af['denominator_clearing_cases']==expected_remainders,'all48 saved remainder cases covered by own80 formal identities')
    expected_signs=[]
    for sign in [-1,1]:
        for e in range(5):
            for t in range(5-e):
                for a in range(5-e-t):
                    for z in range(5-e-t-a):
                        expected_signs.append([sign,e,t,a,z])
    check(af['signed_monomial_cases']==expected_signs,'literal140 signed monomial labels')
    # Recompute every saved Sylvester result using independent permutation determinants.
    for case in saved['diagnostics']['exact_resultant_cases']:
        q,c,f,b=case['parameters']
        conic=substitute(from_records(formal['conic']),dict(Q=num(q),c=num(c),f=num(f),b=num(b)))
        check(resultant_y(conic,from_records(case['H']))==from_records(case['resultant']), 'independent saved resultant '+case['case'])
    for case in saved['diagnostics']['norm_cases']:
        f,d,L=case['f'],case['d'],case['L'];q=c=R=f**3;b=c+R*f*f
        conic=substitute(from_records(formal['conic']),dict(Q=num(q),c=num(c),f=num(f),b=num(b)))
        H=plus(plus(power(var('y'),2*d),prod(num(2),var('T'))),num(-f))
        result=resultant_y(conic,H);K=factorial(2*d+2)*20**(2*d)*(L+1)**2
        check((case['conic_norm'],case['H_norm'],case['resultant_norm'],case['K'])==(norm(conic),norm(H),norm(result),K),'saved norm diagnostics recomputed')
        check(norm(result)<=K*f**(32*d),'actual determinant norm bound')
    for case in saved['diagnostics']['cutoff_cases']:
        if case['branch']=='nonzero_resultant':
            d,L=case['d'],case['L'];K=factorial(2*d+2)*20**(2*d)*(L+1)**2
            check(case['K']==K and case['R_strict_bound']==32*d+4+K.bit_length(),'saved resultant cutoff')
        else:
            check(case['branch']=='zero_resultant','declared cutoff branch')
            t,La,Lb=case['t'],case['LA'],case['LB'];K=La*La+2*Lb*Lb+1
            check(case['K']==K and case['c_strict_bound']==12*t+9+(K-1).bit_length(),'saved rational cutoff')
    check(not any(saved['scope'].values()),'unchanged/no-native-fixture scope flags')
    return dict(all_author_source_fields_checked=True,dependencies_authenticated=saved['pins'],
                all91_dependency_rows_checked=True,full_coefficients_checked=17,zero_coefficients_checked=4,
                actual_conic_and_strong_bindings_checked=True,
                saved_resultants_recomputed=len(saved['diagnostics']['exact_resultant_cases']),
                saved_norm_cases_recomputed=len(saved['diagnostics']['norm_cases']))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--author-root',type=Path);g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
    root=args.root; author=args.author_root or root
    check(len(AUTHOR)==3, 'author pins not frozen')
    pins={}
    for name,wanted in AUTHOR.items():
        actual=sha((author/name).read_bytes());check(actual==wanted,'author pin '+name);pins[name]=actual
    for name,wanted in PROOFS.items():
        actual=sha((root/name).read_bytes());check(actual==wanted,'proof pin '+name);pins[name]=actual
    sourcepath=root/'complete84_scaled_strong_output.json'
    check(sha(sourcepath.read_bytes())==SOURCE_SHA,'actual84 source pin')
    source=read_json(sourcepath)['packet']; original=canonical(source); evidence=source_checks(source)
    author_receipt=read_json(author/'complete84_full_independent_root_absorption.json')
    formal=mathematical_checks()
    corroboration=author_checks(author_receipt,evidence,formal,root)
    check(canonical(source)==original,'own parent packet immutability')
    receipt=dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,
                 dependency_pins=pins,parent_source_sha256=SOURCE_SHA,
                 source=evidence,mathematical=formal,author_comparison=corroboration,
                 policy='Only this newly authored reviewer executes; all author/predecessor programs are inert.')
    if args.output:
        with args.output.open('x') as f:
            f.write(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    else:
        check(canonical(receipt)==canonical(read_json(args.expect)),'exact type-sensitive receipt replay')
    print('PASS full91 source/sign/zero/conic/rational/resultant review')

if __name__=='__main__':main()
