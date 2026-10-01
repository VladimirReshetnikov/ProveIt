"""Already-paid input moduli do not replace Delta in normalized87.

H gives empty valid compiler slices. Eight dyadic-divisible registers
exclude two input residue classes on each actual odd-width compiler slice.
No new universal bound is asserted; the parent source is unchanged.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random
import sympy as sp

import complete75_normalized_strong87 as parent

MODULI = {
    'H': 'a4m5', 'q': 'q', 'q_squared': 'Lbig', 'q_cubed': 'n2',
    'X': 'wn2', 'Y': 'sn2', 'XY': 'UM', 'a': 'R12', 'four_a': 'a4',
}
EXPECTED_INPUT_DEGREES = dict(H=26,q=19,q_squared=20,q_cubed=21,
                             X=22,Y=22,XY=26,a=26,four_a=26)


def sources(modulus='H'):
    assert modulus in MODULI
    _, old, pairs, _ = parent.sources()
    nodes={n:(op,l,r) for n,op,l,r in old}
    assert nodes['index_product']==('*','delta','A')
    assert nodes['index_rhs']==('+','odd_index','index_product')
    nodes['index_product']=('*','delta',MODULI[modulus])
    done=set(parent.RETAINED+parent.eliminated.baseline.prior.CONSTANTS+
             ['x','Bm1','Kconstant','twice_cell_bits'])
    active=set();source=[]
    def visit(n):
        if type(n) is int or n in done:return
        assert n not in active,n
        active.add(n);op,l,r=nodes[n];visit(l);visit(r)
        source.append((n,op,l,r));active.remove(n);done.add(n)
    for l,r in pairs:visit(l);visit(r)
    before={n:(op,l,r) for n,op,l,r in old}
    assert before.keys()==nodes.keys()
    assert {n for n in nodes if nodes[n]!=before[n]}=={'index_product'}
    assert len(source)==86 and pairs==[('eight_units',1)]
    polynomial=source+[('polynomial','-','eight_units',1)]
    assert Counter('M' if op=='*' else 'A' for _,op,_,_ in polynomial)=={'M':48,'A':39}
    return source,pairs,polynomial


def execute(rows,values):
    env=dict(values)
    def get(v):return env[v] if isinstance(v,str) else v
    for n,op,l,r in rows:
        a,b=get(l),get(r)
        env[n]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def pell(A,n):
    chi,psi=1,0
    for _ in range(n):
        chi,psi=A*chi+(A*A-1)*psi,chi+A*psi
    return chi,psi


def source_audit():
    rng=random.Random(87187180);records=[];oldpoly=parent.sources()[3]
    for choice in MODULI:
        source,pairs,poly=sources(choice);counts=Counter()
        for case in range(64):
            signed=case>=32
            v={n:rng.randrange(-7,8) if signed else rng.randrange(1,8)
               for n in parent.RETAINED+['x']}
            B=(16,32,128,256)[case%4]
            fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=B.bit_length()-1,inner_bits=3)
            values=parent.eliminated.fixed_inputs({**v,**fixed})
            old=execute(oldpoly,values);new=execute(poly,values)
            jump=v['delta']*(old[MODULI[choice]]-old['A'])
            correction=2*jump*(old['R12']*old['exponent_rhs']-old['A']*old['index_rhs'])-old['a4m5']*jump*jump
            assert new['index_rhs']==old['index_rhs']+jump
            assert new['exponent_rhs']==old['exponent_rhs']+old['R12']*jump
            assert new['norm_input']==old['norm_input']+correction
            other=1
            for name in parent.FACTOR_NAMES:
                if name!='norm_input':
                    assert old[name]==new[name]
                    other*=old[name]
            assert new['polynomial']==old['polynomial']+other*correction
            product=1
            for name in parent.FACTOR_NAMES:product*=new[name]
            assert product-1==new['polynomial']
            counts['complete_factor_and_output_identities']+=1
            counts['signed_assignments']+=signed
        records.append(dict(modulus=choice,register=MODULI[choice],
            certificate=dict(operations=86,multiplications=48,additions_subtractions=38,equations=1,witnesses=19),
            polynomial=dict(operations=87,multiplications=48,additions_subtractions=39,witnesses=19),
            checks=dict(counts)))
    return records


def degree_audit():
    z=sp.Symbol('z');result=[]
    for choice in MODULI:
        _,_,source=sources(choice);fixtures=[]
        for B,d,offset in ((32,5,0),(128,7,1)):
            scales={n:1+(i+offset)%4 for i,n in enumerate(parent.RETAINED+['x'])}
            scales.update(tau_gap=7,eta=1,zeta=2,Jrep=2,delta=1,rho=3,sigma=2)
            values={n:sp.Poly(scales[n]*z+i+1,z) for i,n in enumerate(parent.RETAINED+['x'])}
            values=parent.eliminated.fixed_inputs({**values,'B':B,'DC':3,'DR':5,'MC':B-2,'MF':4,'cell_bits':d,'inner_bits':3})
            env=execute(source,values)
            degrees=[sp.Poly(env[n],z).degree() for n in parent.FACTOR_NAMES]
            expected=list(parent.FACTOR_DEGREES);expected[2]=EXPECTED_INPUT_DEGREES[choice]
            assert degrees==expected
            assert sp.Poly(env['polynomial'],z).degree()==sum(degrees)
            if choice=='H':
                # a_top=w*s*((B-1)J)^6; its degree is8.
                qtop=(B-1)*scales['Jrep']
                atop=scales['w']*scales['s']*qtop**6
                leading=32*scales['delta']*(scales['rho']-2*scales['delta'])*atop**3
                assert sp.Poly(env['norm_input'],z).LC()==leading and leading
            fixtures.append(dict(B=B,cell_bits=d,factor_degrees=degrees,
                                 polynomial_degree=sum(degrees)))
        result.append(dict(modulus=choice,degree=161+EXPECTED_INPUT_DEGREES[choice],fixtures=fixtures))
    return result


def norm_identity_audit():
    W,a,k,rho,H,delta,M,D=sp.symbols('W a k rho H delta M D')
    mu=W+a*k+rho*H
    norm=mu*mu-(a*a+H)*k*k
    # This is exact without a norm equation or input congruence.
    T=4*W*W-6*W*k-4
    correction=4*norm-4-T
    quotient=sp.expand(correction.subs(a,(H-3)/4)/H)
    assert sp.expand(quotient-(2*W*k+8*W*rho+2*H*k*rho+4*H*rho*rho-4*k*k-6*k*rho))==0
    u=sp.Symbol('u')
    replaced=sp.expand((4*norm-4-(4*W*W-6*W*u-4)).subs(k,u+delta*H).subs(a,(H-3)/4))
    assert sp.Poly(replaced,H).eval(0)==0
    j=delta*(M-D)
    assert sp.expand((mu+a*j)**2-D*(k+j)**2-(mu*mu-D*k*k)-
                     (2*j*(a*mu-D*k)+(a*a-D)*j*j))==0
    return dict(symbolic_input_norm_congruence=True,symbolic_exact_modulus_correction=True,
                divisible_correction_quotient=str(quotient))


def arithmetic_audit():
    congruences=mod8=0
    for A in range(3,45):
        H=4*A-5
        for v in range(1,75):
            chi,psi=pell(A,v)
            E=chi-(A-2)*psi
            assert (E-2**v)%H==0
            assert (4*(2**v)**2-6*(2**v)*psi-4)%H==0
            congruences+=1
            if A%2==0:
                assert psi%2==v%2
                if v%2:assert psi%8==((-1)**((v-1)//2))%8
                mod8+=1
    no_wrap=[]
    for q in (16,17,32,64,256,1024):
        assert 16*q*q+4<4*q**6
        # Exact extremal box bound used in the theorem; no Pell tuple claim.
        if q<=64:
            for W in range(2,q):
                for u in range(3,2*q):
                    T=4*W*W-6*W*u-4
                    assert abs(T)<16*q*q+4 and T!=0
        no_wrap.append(dict(q=q,absolute_bound=16*q*q+4,H_lower_bound=4*q**6))
    inputs=[]
    for d in (5,25,125,625):
      for b in (1,5,25,125):
        rejected=[x for x in range(1,5) if (2*d*x+b)%8 in (3,5)]
        assert len(rejected)==2
        inputs.append(dict(cell_bits=d,inner_offset=b,rejected_input_classes_mod4=[x%4 for x in rejected]))
    return dict(projection_and_norm_congruence_cases=congruences,
                even_parameter_mod8_cases=mod8,H_no_wrap_ranges=no_wrap,
                odd_width_input_class_obstructions=inputs,
                scope='Pell congruences and necessary-domain fixtures only, not complete compiler zeros.')


def verify():
    records=source_audit();degree=degree_audit()
    return dict(status='PASS_COMPLETE75_INPUT_MODULUS_REGISTER_OBSTRUCTIONS',
                default='H',source_records=records,degree_records=degree,
                symbolic=norm_identity_audit(),arithmetic=arithmetic_audit(),
                default_schedule=sources('H')[2],
                conclusions=dict(H='No positive zero on any valid normalized87 compiler slice.',
                    dyadic_divisible_registers='Necessary u=2dx+b is1 or7 modulo8; actual oddd,b therefore omit two input classes modulo4.'),
                scope='Rejected input-modulus substitutions only. Established75/87 unchanged; no universal operation or degree improvement.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=json.loads(json.dumps(verify()))
    path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result
    print(result['status']);print([(v['modulus'],v['degree']) for v in result['degree_records']])
