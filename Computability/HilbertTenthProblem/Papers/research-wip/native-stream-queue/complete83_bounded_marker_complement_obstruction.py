#!/usr/bin/env python3
"""Fresh inert-source audit and independent component evidence; no DAG execution."""
import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path

PINS = {
    'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
    'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
    'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
    'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b',
    'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
    'complete75_positive_transport_projection_obstruction.md': '6fed5e50d1f07039b0243c40ae712dc4e618b821d308327d36d05803d8a94ee8',
    'complete75_positive_complement86_all_input_collapse.md': '8a1049e155f0ce8b59ab10c7f7bd7ef69b82798e56888beafed1ff5e35cbc1da',
    'complete83_outer_slack_collapse.md': '6623a525ab1b0376b1d6a452f8e5618f8e1f64f0a255fdcbcc97611dd3598259',
    'complete86_marked_word_obstruction.md': '86f3a8beb0cf83d2ff239475a9a2981dec6cbd7fb12577584d9ffb2ca5dd8c76',
    'complete75_input_bound_absorption_obstruction.md': '6194e2ac1f9f38a8be1bf21f47891373fb1dc52446ca30b915140fc243a607ae',
}

def require(test, message):
    if not test:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()

def integer_pin(n):
    require(n >= 0, 'nonnegative integer pin')
    return {'bits': n.bit_length(), 'population': n.bit_count(),
            'hex_sha256': digest(format(n, 'x').encode())}

def source_audit(root):
    for name, sha in PINS.items():
        require(digest((root/name).read_bytes()) == sha, 'dependency pin '+name)
    parent = json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
    old = parent['source']
    old_by_name = {row[0]: row for row in old}
    require(len(old) == len(old_by_name) == 84, 'parent source size')
    require(old_by_name['q_minus_F'] == ['q_minus_F', '-', 'q', 'F'], 'deleted row')
    changes = {
        'q_minus_FZ': ['q_minus_FZ', '-', 'q', 'Z'],
        'C_after_alpha': ['C_after_alpha', '-', 'q_minus_FZ', 'outer_beta'],
        'gap_product': ['gap_product', '*', 'q', 'outer_complement'],
        'gap': ['gap', '-', 'gap_product', 'Z'],
        'transport_partial': ['transport_partial', '+', 'innerC', 'outer_complement'],
    }
    expected_old = {
        'q_minus_FZ': ['q_minus_FZ', '-', 'q_minus_F', 'Z'],
        'C_after_alpha': ['C_after_alpha', '-', 'q_minus_FZ', 'alpha'],
        'gap_product': ['gap_product', '*', 'repunit', 'q_minus_F'],
        'gap': ['gap', '+', 'gap_product', 'q_minus_FZ'],
        'transport_partial': ['transport_partial', '+', 'innerC', 'q_minus_F'],
    }
    for name, row in expected_old.items():
        require(old_by_name[name] == row, 'literal boundary '+name)
    rows = [changes.get(row[0], row) for row in old if row[0] != 'q_minus_F']
    rename = {'F': 'outer_complement', 'alpha': 'outer_beta'}
    free = [rename.get(name, name) for name in parent['free']]
    witnesses = [rename.get(name, name) for name in parent['witnesses']]
    available = set(free)
    for name, op, left, right in rows:
        require(name not in available and op in ['+', '-', '*'], 'row name/op')
        require(all(isinstance(v, int) or v in available for v in [left, right]), 'topology '+name)
        available.add(name)
    by_name = {row[0]: row for row in rows}
    live = set()
    pending = [parent['output']]
    while pending:
        name = pending.pop()
        if isinstance(name, int) or name in live:
            continue
        live.add(name)
        if name in by_name:
            pending.extend(by_name[name][2:])
    require(set(by_name) <= live and set(free) <= live, 'whole graph liveness')
    count = Counter(row[1] for row in rows)
    literal = sum(row == old_by_name[row[0]] for row in rows)
    require(len(rows) == 83 and count['*'] == 47 and count['+']+count['-'] == 36, 'child ledger')
    require(literal == 78 and len(witnesses) == 18 and len(free) == 25, 'retained/interface count')
    require(rows[-7:] == old[-7:], 'complete finalizer retained')
    return {
        'source': rows, 'source_data_sha256': digest(canonical(rows)),
        'free': free, 'witnesses': witnesses, 'ordinary_input': 'x',
        'fixed_numerals': parent['fixed_numerals'], 'output': parent['output'],
        'factors': parent['factors'], 'ledger': {'M': 47, 'A': 36, 'total': 83},
        'deleted': old_by_name['q_minus_F'],
        'edits': [{'before': expected_old[n], 'after': changes[n]} for n in changes],
        'literal_retained_rows': literal, 'all_rows_and_ports_live': True,
        'exact_degree_by_invertible_affine_substitution': 187,
        'array_evaluations': 0, 'status': 'REJECTED: full positive projection is all x>=1',
        'parent_restore': {'F': 'q-outer_complement', 'alpha': 'outer_beta-q+outer_complement'},
        'full_output_relation': 'P83=P84(F=q-U,alpha=beta-q+U)',
        'private_retained_value_exceptions': ['q_minus_FZ', 'gap_product'],
    }

# Independent sparse polynomial arithmetic at the small handwritten cut.
NV = 8
def const(n):
    return {(0,)*NV: n} if n else {}
def variable(index):
    e = [0]*NV
    e[index] = 1
    return {tuple(e): 1}
def add(a, b, sign=1):
    c = dict(a)
    for mon, val in b.items():
        c[mon] = c.get(mon, 0)+sign*val
    return {mon: val for mon, val in c.items() if val}
def sub(a, b):
    return add(a, b, -1)
def mul(a, b):
    c = {}
    for m, x in a.items():
        for n, y in b.items():
            k = tuple(i+j for i, j in zip(m, n))
            c[k] = c.get(k, 0)+x*y
    return {mon: val for mon, val in c.items() if val}

def local_identities():
    q, U, beta, Z, tx, K, w, tq = [variable(i) for i in range(NV)]
    Fold = sub(q, U)
    alphaold = add(sub(beta, q), U)
    parentU = sub(q, Fold)
    parentV = sub(parentU, Z)
    parentC = sub(sub(parentV, alphaold), tx)
    childC = sub(sub(sub(q, Z), beta), tx)
    parentgap = add(mul(sub(q, const(1)), parentU), parentV)
    childgap = sub(mul(q, U), Z)
    parentNt = sub(add(mul(add(K, w), parentC), parentU), mul(tq, sub(q, const(1))))
    childNt = sub(add(mul(add(K, w), childC), U), mul(tq, sub(q, const(1))))
    pairs = {'U': (parentU,U), 'C': (parentC, childC), 'gap': (parentgap,childgap),
             'transport': (parentNt,childNt), 'forward_beta': (add(Fold,alphaold),beta)}
    for name, (a,b) in pairs.items():
        require(a == b, 'polynomial identity '+name)
    return {'variables': ['q','U','beta','Z','ell*x','K','w','t_transport'],
            'identities': list(pairs), 'all_ring': True, 'saved_array_used': False}

def outer_cases():
    answer = []
    for d in range(4, 11):
        L = math.lcm(*range(1, d+1))
        D = L
        while D % 2 == 0:
            D //= 2
        B = 1 << d
        for mask_choice in range(3):
            MC = 2+4*mask_choice
            MF = B-1+4+8*mask_choice
            # Small d may not fit the larger native-MF choice.
            if MF-(B-1) >= B-1:
                continue
            K = 17*B+7+2*mask_choice
            b = 3+2*mask_choice
            for x in [1,2,5,13]:
                u = 2*d*x+b
                W = 1 << u
                M = 8
                while (D*M) % L or (1 << (D*M)) <= W+2*M+2*d*x:
                    M *= 2
                t = D*M
                q = 1 << t
                J = (q-1)//(B-1)
                require((q-1) % (B-1) == 0 and (q-1) % D == 0, 'period host')
                e = 3 if D == 1 else 3+4*(((MC+MF)*J-3)*pow(4,-1,D) % D)
                Z = 1+(e-MC*J-1) % M
                C = Z+W
                beta = q-2*Z-W-2*d*x
                U0 = 1+(-((K+(1 << e))*C)) % (q-1)
                mask = (MC+q*MF)*J
                R0 = (q*U0-Z)*(q*q-1)+mask
                S = q*(q*q-1)*(q-1)
                l0 = R0//S+1
                D0 = S*l0-R0
                N = max(D0.bit_length()+1, 4*t+u+8,
                        3*t+2+(D0-1).bit_count()-(S-1).bit_count(),
                        (l0+3).bit_length()+1)
                ell = (1 << N)-l0
                U = U0+(q-1)*ell
                R = R0+S*ell
                pc = (S-1).bit_count()+N-(D0-1).bit_count()
                require(0 < Z <= M and 0 < e < t and beta > 0, 'positive small-marker setup')
                require(C+Z+2*d*x < q and C-Z == W, 'retained width/input')
                require(R == S*(1 << N)-D0 and R.bit_count() == pc, 'complement identity')
                require(R % t == e and R % 4 == 3, 'full index residues')
                require(U > q and R > max(q**4,3*q+1,3*t,u,e) and pc >= 3*t+2, 'tail thresholds')
                require(((K+(1 << e))*C+U-1) % (q-1) == 0, 'current transport residue')
                require(beta+U-q > 0, 'restored alpha positive')
                answer.append({'d':d,'b':b,'K':K,'MC':MC,'MF_source':MF,'x':x,
                               'D':D,'M':M,'t':t,'e':e,'Z':Z,'N':N,
                               'q':integer_pin(q),'U':integer_pin(U),'beta':integer_pin(beta),
                               'R':integer_pin(R),'population_threshold':3*t+2})
    return {'scope':'synthetic fixed numeral controls, not compiled programs; no X=2^R or full witnesses materialized',
            'cases': answer, 'count': len(answer)}

def pell(parameter, index):
    require(parameter >= 2 and index >= 0, 'Pell arguments')
    c0,c1 = 1,parameter
    s0,s1 = 0,1
    if index == 0:
        return c0,s0
    for _ in range(1,index):
        c0,c1 = c1,2*parameter*c1-c0
        s0,s1 = s1,2*parameter*s1-s0
    return c1,s1

def components():
    first_main = []
    input_count = 0
    for R in [7,11,15,19]:
        r = (R-1)//2
        X = 1 << R
        MR = sum(math.comb(2*r,r+j)*X**j for j in range(r+1))
        require(MR % 2 == 0, 'half-binomial parity')
        Y = MR//2
        v2Y = (Y & -Y).bit_length()-1
        require(v2Y == R.bit_count()-2, 'half-binomial valuation')
        a = Y*(X+1)
        A = a+2
        Delta = A*A-1
        H = 4*a+3
        E = X*Y
        P = 2*X*Y*Y+1
        Dmain,c = pell(A,R)
        tau,khalf = pell(P,r+1)
        k = 2*khalf
        eta = c-k*Y
        zeta = k-eta
        require(eta > 0 and zeta > 0 and (k-R-1) % E == 0 and k-R-1 > 0, 'strict ratio/index')
        require(tau*tau-(X*Y*Y*k)*(X*Y*Y*k+k) == 1, 'actual first factor')
        gamma_num = Dmain-X-a*c
        require(gamma_num % H == 0 and gamma_num > 0 and Dmain*Dmain-Delta*c*c == 1, 'main factor')
        gamma = gamma_num//H
        gs = [0,0]
        for j in range(R-1):
            gs.append(2*A*gs[-1]-gs[-2]+(1 << j))
        require(gs[R] == gamma and all(gs[j+1] > gs[j] for j in range(1,R)), 'gamma recurrence')
        for u in range(3,R,2):
            mu,kappa = pell(A,u)
            delta = (kappa-u)//Delta
            rho = gs[u]
            sigma = gamma-rho
            require(delta > 0 and (kappa-u) % Delta == 0 and rho > 0 and sigma > 0, 'positive input split')
            require(mu == (1 << u)+a*kappa+rho*H and mu*mu-Delta*kappa*kappa == 1, 'input factor')
            input_count += 1
        first_main.append({'R':R,'valuation_Y':v2Y,'Y':integer_pin(Y),'c':integer_pin(c)})
    aux = []
    for A in range(2,7):
        R = 3
        Delta = A*A-1
        _,c = pell(A,R)
        m = 2*c*R
        f,psi = pell(A,m)
        require(psi % (c*c) == 0, 'normalized coefficient integer')
        i = psi//(c*c)
        S = Delta*psi
        chi,y = pell(S,R)
        require(chi % S == 0, 'odd auxiliary index')
        V = chi//S
        numerator = V+c+R*f*f
        require(numerator % (c*f) == 0, 'Bezout quotient integral')
        T = numerator//(c*f)
        require(i > 0 and T > 0 and y > 0, 'positive auxiliaries')
        require(c*(T*f-1)-R*f*f == V, 'actual auxiliary argument')
        require(S*S == Delta*(f*f-1) and Delta*f*f-S*S == Delta, 'actual scaled strong')
        require(S*S*(V*V-y*y)+y*y == 1, 'actual auxiliary norm')
        aux.append({'A':A,'R':R,'m':m,'i':integer_pin(i),'T':integer_pin(T),'f':integer_pin(f)})
    return {'scope':'handwritten local Pell diagnostics only; no source-array evaluation or complete compiler fixture',
            'first_main':first_main,'input_splits':input_count,'normalized_auxiliary':aux}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--write',type=Path)
    ap.add_argument('--expect',type=Path)
    args = ap.parse_args()
    require(not (args.write and args.expect), 'choose write or expect')
    result = {'status':'PASS', 'scope':'Rejected complete83 combined coordinate chart; source arrays inert throughout',
              'dependencies':PINS, 'candidate':source_audit(args.root),
              'local_identities':local_identities(),'outer':outer_cases(),'components':components(),
              'program_execution':{'predecessors':False,'supplied':False,'parent_array':False,'candidate_array':False},
              'helper_sha256':digest(Path(__file__).read_bytes())}
    data = (json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
    if args.write:
        args.write.write_bytes(data)
    if args.expect:
        require(data == args.expect.read_bytes(), 'exact receipt reproduction')
    print(json.dumps({'status':'PASS','rows':83,'outer_cases':result['outer']['count'],
                      'input_splits':result['components']['input_splits'],
                      'receipt_sha256':digest(data)},sort_keys=True))

if __name__ == '__main__':
    main()
