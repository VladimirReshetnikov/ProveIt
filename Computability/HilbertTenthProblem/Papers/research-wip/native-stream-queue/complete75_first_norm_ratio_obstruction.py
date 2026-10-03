"""An apparent 87-operation recoding accepts every positive input.

An explicit outer CRT construction extends to full positive zeros by
Pell formulas. The enormous full witness towers are supplied parametrically.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import complete75_coupled_index_linear88 as parent

eliminated = parent.eliminated
RETAINED = ['first_index_gap' if name == 'zeta' else name for name in parent.RETAINED]


def sources():
    _, old, pairs, _ = parent.sources()
    nodes = {name: (op, left, right) for name, op, left, right in old}
    assert nodes['R10b'] == ('+', 'eta', 'zeta')
    assert nodes.pop('first_signed_gap') == ('-', 'twice_tau_gap', 'R10b')
    assert nodes['first_cross'] == ('*', 'first_root_base', 'first_signed_gap')
    assert nodes['norm_first'] == ('+', 'tau_square', 'first_cross')
    nodes['R10b'] = ('+', 'twice_tau_gap', 'first_index_gap')
    nodes['first_cross'] = ('*', 'first_root_base', 'first_index_gap')
    nodes['norm_first'] = ('-', 'tau_square', 'first_cross')
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    active, certificate = set(), []

    def visit(name):
        if isinstance(name, int) or name in available:
            return
        assert name not in active
        active.add(name)
        op, left, right = nodes[name]
        visit(left)
        visit(right)
        certificate.append((name, op, left, right))
        active.remove(name)
        available.add(name)

    for left, right in pairs:
        visit(left)
        visit(right)
    assert len(certificate) == len(nodes) == 86
    return certificate, pairs, certificate+[('polynomial', '-', 'eight_units', 1)]


def source_checks():
    certificate, pairs, polynomial = sources()
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert counts == {'M':47, 'A':40}
    old = parent.sources()[3]
    rng, evidence = random.Random(875141), Counter()
    for case in range(512):
        signed = case >= 384
        supplied = {name: rng.randrange(-8,9) if signed else rng.randrange(1,9)
                    for name in RETAINED+['x']}
        B = rng.choice((16,32,64,256))
        supplied.update(B=B, cell_bits=B.bit_length()-1, inner_bits=3,
                        MC=B-2, MF=4, DC=3, DR=5)
        restored = {**supplied,
                    'zeta': 2*supplied['tau_gap']+supplied['first_index_gap']-supplied['eta']}
        newenv = eliminated.run(polynomial, eliminated.fixed_inputs(supplied))
        oldenv = eliminated.run(old, eliminated.fixed_inputs(restored))
        assert newenv['polynomial'] == oldenv['polynomial']
        assert all(newenv[name] == oldenv[name] for name in parent.FACTOR_NAMES)
        assert all(newenv[name] == oldenv[name] for name, _, _, _ in certificate
                   if name != 'first_cross')
        assert newenv['first_cross'] == -oldenv['first_cross']
        evidence['signed_supplied' if signed else 'positive_supplied'] += 1
        evidence['nonpositive_restored_zeta'] += restored['zeta'] <= 0
    return dict(operations=87, multiplications=47, additions_subtractions=40,
                positive_supplied_coordinates=19, certificate_operations=86,
                comparisons=pairs, polynomial_schedule=polynomial,
                unconditional_parent_coordinate_identities=512,
                coordinate_map='zeta_old=2*tau_gap+first_index_gap-eta',
                evidence=dict(evidence),
                status='Rejected: an explicit positive extension accepts every ordinary input.')


def pell(A, n):
    """Exact binary powering in Z[sqrt(A*A-1)]."""
    D = A*A-1
    x, y, u, v = 1, 0, A, 1
    while n:
        if n & 1:
            x, y = x*u+D*y*v, x*v+y*u
        u, v = u*u+D*v*v, 2*u*v
        n //= 2
    return x, y


def small_y_main(q, R):
    X, Y = 2**R, q**3
    a, E = Y*(X+1), X*Y
    A, V = a+2, X*Y*Y
    P, n = 2*V+1, (R+1)//2
    d, c = pell(A, R)
    tau, half_k = pell(P, n)
    _, previous = pell(P, n-1)
    k, g, gap = 2*half_k, half_k-previous, 2*previous
    eta = c-k*Y
    h, hrem = divmod(k-R-1,E)
    gamma, grem = divmod(d-X-a*c,4*a+3)
    assert hrem == grem == 0
    assert all(value > 0 for value in (X,Y,a,c,d,k,tau,g,gap,eta,h,gamma))
    assert k == 2*g+gap and tau == V*k+g
    assert g*g-E*(k*Y)*gap == 1
    assert tau*tau-V*(V+1)*k*k == 1
    assert d*d-(A*A-1)*c*c == 1
    assert c == k*Y+eta and k == R+1+h*E
    assert d == X+a*c+gamma*(4*a+3)
    assert c > k*(Y+1) and eta > k
    return dict(q=q, R=R, X=X, Y=Y, a=a, A=A, E=E, P=P, c=c, d=d,
                k=k, tau=tau, tau_gap=g, first_index_gap=gap, eta=eta,
                h=h, gamma=gamma, restored_zeta=k-eta)


def theorem_domain_checks():
    evidence = []
    for t in range(4,9):
        q = 2**t
        R = 3*q+3
        z = small_y_main(q,R)
        assert q >= 16 and 3*q+1 <= R < q**4 and R % 4 == 3
        assert z['X'] % q**3 == z['Y'] % q**3 == 0
        assert R.bit_count() == 4 < 3*t+2
        evidence.append(dict(q=q,R=R,popcount_R=4,required_population=3*t+2,
                             all_main_equations=True, all_new_main_coordinates_positive=True,
                             restored_zeta_negative=True,
                             bit_lengths={name:z[name].bit_length() for name in
                                          ('c','k','tau_gap','first_index_gap','eta')}))
    return dict(main_fixtures=evidence,
                full_strong_auxiliary_extension='Parametric proof; towers not materialized in these fixtures.',
                scope='Valid external q/R scale hypotheses; not complete outer compiler/input tuples.')


def input_reextension_checks():
    cases = 0
    for t in range(4,7):
        q = 2**t
        z = small_y_main(q,3*q+3)
        A,a,H = z['A'],z['a'],4*z['a']+3
        Delta = A*A-1
        for u in range(3,min(z['R'],43),2):
            root,kappa = pell(A,u)
            delta, drem = divmod(kappa-u,Delta)
            rho, rrem = divmod(root-a*kappa-2**u,H)
            sigma = z['gamma']-rho
            assert drem == rrem == 0 and min(delta,rho,sigma)>0
            assert 2**u+a*kappa+rho*H == root
            assert root*root-Delta*kappa*kappa == 1
            assert kappa < z['c']
            cases += 1
    return dict(exact_positive_input_extension_cases=cases,
                scope='Main and input components at a common base; full outer compiler tuples remain parametric.')


def all_input_outer(x,d,b,MC,MF,DC,DR):
    B,K0 = 2**d,DC+2**d*DR
    odd_part = d
    while odd_part % 2 == 0:
        odd_part //= 2
    valuation = (d//odd_part).bit_length()-1
    u,W = 2*d*x+b,2**(2*d*x+b)
    step = 0
    while True:
        width = d*2**step
        two_part = 2**(valuation+step)
        if two_part >= 4 and width > 4*odd_part:
            q = 2**width
            J = (q-1)//(B-1)
            target = ((q*q+W)*(q*q-1)+(MC+q*(MF+B-1))*J) % odd_part
            residue = next(e for e in range(3,4*odd_part,4) if e % odd_part == target)
            Cbase = odd_part*((residue+W-MC*J)*pow(odd_part,-1,two_part) % two_part)
            C = W+1+(Cbase-W-1) % width
            Z = C-W
            F = (K0+2**residue)*C
            alpha = q-C-Z-F-2*d*x
            if alpha > 0:
                break
        step += 1
    R = (q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
    assert W < C <= W+width and C % odd_part == 0
    assert C % two_part == (residue+W-MC*J) % two_part
    assert 0 <= residue < 4*odd_part < width
    assert R % width == residue and R % 4 == 3
    assert 3*q+1 < R < q**4 and R > max(u,3*width,residue)
    assert pow(2,R,q-1) == 2**residue
    assert min(J,F,Z,alpha,C) > 0
    return dict(B=B,cell_bits=d,inner_bits=b,MC=MC,MF=MF,DC=DC,DR=DR,x=x,
                Jrep=J,F=F,Z=Z,alpha=alpha,q=q,C=C,W=W,R=R,
                width=width,two_part=two_part,odd_part=odd_part,
                residue=residue,step=step,u=u)


def all_input_outer_checks():
    polynomial = sources()[2]
    nodes = {name:(op,left,right) for name,op,left,right in polynomial}
    wanted = set()

    def need(name):
        if not isinstance(name,str) or name not in nodes or name in wanted:
            return
        wanted.add(name)
        _,left,right=nodes[name]
        need(left)
        need(right)

    for name in ('q','r_lhs','marked_rhs','W'):
        need(name)
    outer_source = [row for row in polynomial if row[0] in wanted]
    rng, cases, largest_width = random.Random(870419),0,0
    fixtures = []
    for d in range(4,25):
        B=2**d
        for x in range(1,9):
            overlap_transfer=sum(2**j for j in range(3,d) if rng.randrange(2))
            MC,MF=B-2-overlap_transfer,4+overlap_transfer
            assert MC % 4 == 2 and MF % 8 == 4
            assert 0 < MC < B-1 and 0 < MF < B-1
            assert MC.bit_count()+MF.bit_count() == d
            z=all_input_outer(x,d,rng.choice((1,3,5,7)),MC,MF,
                              rng.randrange(1,30),rng.randrange(1,30))
            supplied={name:1 for name in RETAINED+['x']}
            supplied.update({name:z[name] for name in z
                             if name in RETAINED+eliminated.baseline.prior.CONSTANTS+['x']})
            env=eliminated.run(outer_source,eliminated.fixed_inputs(supplied))
            assert env['q']==z['q'] and env['r_lhs']==z['R']
            assert env['marked_rhs']==z['C'] and env['W']==z['W']
            largest_width=max(largest_width,z['width'])
            if x==1 and d<=8:
                fixtures.append({name:z[name] for name in
                                 ('cell_bits','x','width','odd_part','two_part','residue','step')})
            cases+=1
    return dict(arbitrary_input_positive_outer_constructions=cases,
                exact_actual_source_outer_identities=cases,
                varied_compiler_admissible_masks=True,largest_checked_width=largest_width,
                sample_parameters=fixtures,
                transport='X=2^R, zplus=1+C*(X-2^residue)/(q-1)>1; numerator divisibility checked modulo q-1.',
                scope='Exact outer registers and congruences materialized. Full positive Pell extensions are parametric.')


def materialized_prototype():
    # A complete modified kernel tuple, outside q>=16, to audit its full
    # auxiliary extension numerically without astronomical witness towers.
    z = small_y_main(1,3)
    A,c,R = z['A'],z['c'],z['R']
    Delta, m = A*A-1, 2*c*R
    f, v = pell(A,m)
    i, rem = divmod(Delta*v,c*c)
    assert rem == 0 and i > 0
    T = i*c*c
    chi, y = pell(T,R)
    U, rem = divmod(chi,T)
    assert rem == 0
    j, jrem = divmod(U+R,c)
    o, orem = divmod(U+c,f)
    assert jrem == orem == 0 and min(f,i,T,U,j,o,y)>0
    assert T*T == Delta*(f*f-1)
    assert T*T*(U*U-y*y) == 1-y*y
    assert U == j*c-R == o*f-c
    assert z['restored_zeta'] < 0
    return dict(q=1,R=3,X=z['X'],Y=z['Y'],a=z['a'],c=c,k=z['k'],
                tau=z['tau'],tau_gap=z['tau_gap'],first_index_gap=z['first_index_gap'],
                eta=z['eta'],restored_zeta=z['restored_zeta'],h=z['h'],gamma=z['gamma'],
                auxiliary_index=m, all_retained_kernel_equations=True,
                all_new_supplied_coordinates_positive=True,
                auxiliary_bit_lengths={name:value.bit_length() for name,value in
                                       dict(f=f,i=i,j=j,o=o,y=y).items()},
                scope='Full modified kernel prototype; outside the external q>=16 hypotheses.')


def first_norm_checks():
    cases = 0
    for V in range(1,33):
        P = 2*V+1
        for n in range(2,15):
            tau, psi = pell(P,n)
            _, previous = pell(P,n-1)
            k, g, gap = 2*psi, psi-previous, 2*previous
            assert min(g,gap)>0
            assert tau-V*k == g and k == 2*g+gap
            assert g*g-V*k*gap == 1
            cases += 1
    return dict(positive_forward_coordinate_cases=cases,
                forward_map='first_index_gap=k-2*tau_gap=2*psi_P(n-1)')


def verify():
    return dict(status='PASS_ALL_INPUT_UPPER_RATIO_OBSTRUCTION',source=source_checks(),
                first_norm=first_norm_checks(),theorem_domain=theorem_domain_checks(),
                input_reextension=input_reextension_checks(),
                all_input_outer=all_input_outer_checks(),
                complete_small_kernel=materialized_prototype(),
                established_universal_bounds_unchanged=dict(comparison=75,polynomial=88),
                exact_projection='Every positive ordinary input for every fixed compiled constant tuple.',
                limit='This exact one-addition rewrite is rejected; no impossibility of other 87-operation formulas is asserted. '
                      'The complete enormous witness tuples are given by formulas, not numerically materialized.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt',action='store_true')
    args=parser.parse_args()
    result=verify()
    path=Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        assert json.loads(path.read_text()) == json.loads(json.dumps(result))
    print(result['status'])
