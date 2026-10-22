#!/usr/bin/env python3
"""Independent bounded algebra checks for the 26-integer circuit.

The only local module imported is build_integer26.py. All validation uses
explicit exceptions and remains active under python -O. The four numeral
ports in these tests are synthetic algebraic fixtures, not expanded K215
coefficients and not claimed to encode a ZFC refutation.
"""
import argparse
import hashlib
import itertools
import json
from math import isqrt
from pathlib import Path
import random

import build_integer26 as builder

GUARDS=('J','F','alpha','z','s','eta','zeta')
RAW=tuple(name+'_'+axis for name in GUARDS for axis in ('x','y','z'))+(
    'h','i_raw','T','w_raw','t')
FIXED=('Bm1','Kconstant','MC','MF')
PRIME=1000003
SEED=2600261022
GROUPS=('signed_nonzero_scale','zero_scale_signed_T',
        'zero_T_nonzero_scale','zero_scale_zero_T')


def require(condition,message):
    if not condition:
        raise RuntimeError(message)


def validate_packet(packet):
    require(tuple(packet['witnesses'])==RAW,'Unexpected 26-variable order')
    require(tuple(packet['fixed_numerals'])==FIXED,'Unexpected coefficient ports')
    require(packet['domain']=='unrestricted integers','Incorrect domain metadata')
    known=set(RAW+FIXED)
    counts={'+':0,'-':0,'*':0}
    for node,op,left,right in packet['source']:
        require(node not in known,'Duplicate circuit name: '+node)
        require(op in counts,'Unsupported circuit operation')
        require(all(isinstance(x,int) or x in known for x in (left,right)),
                'Undefined circuit operand at '+node)
        known.add(node)
        counts[op]+=1
    ledger=packet['ledger']
    require(ledger['operations']==len(packet['source']),'Operation ledger mismatch')
    require(ledger['multiplications']==counts['*'],'Multiplication ledger mismatch')
    require(ledger['additions_subtractions']==counts['+']+counts['-'],
            'Addition/subtraction ledger mismatch')
    return {'operations':len(packet['source']),
            'multiplications':counts['*'],
            'additions_subtractions':counts['+']+counts['-']}


def interpret(packet,inputs,modulus):
    """Independent interpreter; builder.evaluate is deliberately not used."""
    values={key:value%modulus for key,value in inputs.items()}
    for node,op,left,right in packet['source']:
        a=left if isinstance(left,int) else values[left]
        b=right if isinstance(right,int) else values[right]
        if op=='+':value=a+b
        elif op=='-':value=a-b
        elif op=='*':value=a*b
        else:raise RuntimeError('Unsupported operation in interpreter')
        values[node]=value%modulus
    return values


def named(packet,values,name,modulus):
    require(name in packet['named_registers'],'Missing named register: '+name)
    port=packet['named_registers'][name]
    return (port if isinstance(port,int) else values[port])%modulus


def independent_prefix(raw,modulus):
    """The mathematical formulas, independently written from the proof."""
    p=modulus
    v={key:value%p for key,value in raw.items()}
    for name in GUARDS:
        x,y,z=(raw[name+'_'+axis] for axis in ('x','y','z'))
        v[name]=(x*x+x+y*y+z*z+1)%p
    v['i']=(2*raw['i_raw']+1)%p
    v['w']=raw['w_raw']**2%p
    out={}
    def put(key,value):
        out[key]=value%p
        return out[key]
    q=put('q',v['Bm1']*v['J']+1)
    Cw=put('Cword',q-v['F']-v['alpha'])
    X=put('X',v['w']*q)
    Y=put('Y',v['s']*q**3)
    E=put('E',X*Y)
    k=put('k',v['eta']+v['zeta'])
    c=put('c',k*Y+v['eta'])
    a=put('a',E+Y)
    H=put('H',4*a+3)
    Delta=put('Delta',a*a+H)
    R=put('R',((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)
                 +(v['MC']+q*v['MF'])*v['J'])
    put('Nk',k-v['h']*E-R)
    put('Nt',(v['Kconstant']+v['w'])*Cw+q-v['F']-v['z']*(q-1))
    ell=put('ell',E*k*Y)
    put('A',1+ell*(ell+k))
    I=put('I',v['i']*c*c)
    D=put('D',1+Delta*I*I)
    Q=put('Q',(Delta*I)**2)
    put('d',Q-1)
    vv=put('v',c*v['T'])
    Z=put('Z',c+R*D)
    put('e',Q*(D*vv*vv+Z*Z)-1)
    put('B',2*Q*vv*Z)
    put('b',X+a*c)
    put('G',Delta*c*c+1)
    g=put('gamma_bound',c+X)
    u=put('tau_bound',ell+k)
    C=put('Cbound',vv*vv+D+Z)
    rf=put('f_bound',(a+2)*(v['i']*v['i']+1)*c*c)
    C2=put('ratio_bound',c*(v['T']*v['T']+1)+c+R*rf)
    at=put('weight_tau',2*g+1)
    S=put('Sbound',at*u+g)
    ay=put('weight_y',Q*C*S+1)
    put('weight_f',2*ay*C2+S+1)
    return out


def compare_prefix(packet,values,prefix,modulus):
    for key,expected in prefix.items():
        actual=named(packet,values,key,modulus)
        require(actual==expected,'Independent prefix mismatch: '+key)


def sqrt_mod(value,prime):
    value%=prime
    root=pow(value,(prime+1)//4,prime)
    return root if root*root%prime==value else None


def branch_sums(prefix,prime,tau_weight=None):
    H,d=prefix['H'],prefix['d']
    if H*d%prime==0:
        return None
    f0=sqrt_mod(prefix['D'],prime)
    tau0=sqrt_mod(prefix['A'],prime)
    gamma0=sqrt_mod(prefix['G'],prime)
    if any(x is None or x==0 for x in (f0,tau0,gamma0)):
        return None
    dinv=pow(d,-1,prime)
    hinv=pow(H,-1,prime)
    at=prefix['weight_tau'] if tau_weight is None else tau_weight
    sums=[]
    for f in (f0,(-f0)%prime):
        y0=sqrt_mod((prefix['e']-prefix['B']*f)*dinv,prime)
        if y0 is None or y0==0:
            return None
        for st,sy,sg in itertools.product((1,-1),repeat=3):
            gamma=(sg*gamma0-prefix['b'])*hinv%prime
            sums.append((gamma+at*st*tau0+prefix['weight_y']*sy*y0
                         +prefix['weight_f']*f)%prime)
    require(len(sums)==16,'Incomplete radical branch product')
    return sums


def product_value(prefix,sums,t,prime):
    value=pow(prefix['d'],8,prime)*pow(prefix['H'],16,prime)%prime
    for root in sums:
        value=value*(t-root)%prime
    return value


def t_degree_upper_bound(packet,output):
    """A small circuit check in t only; no total-degree expansion is run."""
    degrees={name:(1 if name=='t' else 0) for name in RAW+FIXED}
    for node,op,left,right in packet['source']:
        dl=0 if isinstance(left,int) else degrees[left]
        dr=0 if isinstance(right,int) else degrees[right]
        degrees[node]=dl+dr if op=='*' else max(dl,dr)
    return degrees[output]


def inputs_for(group,index,rng):
    values={name:rng.randint(-12,12) for name in RAW}
    values.update({name:rng.randint(1,100) for name in FIXED})
    # Every group deliberately includes both signs of the odd multiplier.
    values['i_raw']=rng.randint(0,30) if index%2==0 else -rng.randint(1,30)
    values['T']=rng.randint(1,30)*(1 if (index//2)%2==0 else -1)
    values['w_raw']=rng.randint(1,30)*(1 if index%2==0 else -1)
    if group in ('zero_scale_signed_T','zero_scale_zero_T'):
        values['w_raw']=0
    if group in ('zero_T_nonzero_scale','zero_scale_zero_T'):
        values['T']=0
    return values


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--receipt',type=Path,
        default=Path(__file__).resolve().with_name('integer26_independent_verification.json'))
    args=parser.parse_args()
    require(PRIME%4==3 and all(PRIME%d for d in range(2,isqrt(PRIME)+1)),
            'Finite-field modulus is not an appropriate prime')
    system,product,sos=builder.build()
    ledgers={packet['name']:validate_packet(packet) for packet in (system,product,sos)}
    norm_port=system['named_registers']['primitive_norm']
    require(t_degree_upper_bound(system,norm_port)==16,
            'Unexpected degree bound in the compressed coordinate')
    rng=random.Random(SEED)
    fixture_counts={group:0 for group in GROUPS}
    attempts_by_group={group:0 for group in GROUPS}
    signs={'i_positive':0,'i_negative':0,'T_positive':0,'T_negative':0,
           'T_zero':0,'w_positive':0,'w_zero':0}
    factor_checks=root_checks=finalizer_checks=prefix_checks=0
    missing_tau_weight_detected=False
    for group in GROUPS:
        while fixture_counts[group]<16 and attempts_by_group[group]<8000:
            attempts_by_group[group]+=1
            inputs=inputs_for(group,fixture_counts[group],rng)
            prefix=independent_prefix(inputs,PRIME)
            sums=branch_sums(prefix,PRIME)
            if sums is None:
                continue
            values=interpret(system,inputs,PRIME)
            compare_prefix(system,values,prefix,PRIME)
            prefix_checks+=1
            # Seventeen distinct t-values certify the entire degree<=16
            # polynomial identity for this one finite-field parameter tuple.
            for t in range(17):
                trial=dict(inputs,t=t)
                actual=interpret(system,trial,PRIME)[norm_port]
                expected=product_value(prefix,sums,t,PRIME)
                require(actual==expected,
                        'Full sixteen-branch norm mismatch in '+group)
                factor_checks+=1
                pv=interpret(product,trial,PRIME)[product['output']]
                sv=interpret(sos,trial,PRIME)[sos['output']]
                require(pv==(prefix['Nk']*prefix['Nt']*(1+actual)-1)%PRIME,
                        'Product finalizer mismatch')
                require(sv==((prefix['Nk']-1)**2+(prefix['Nt']-1)**2+actual*actual)%PRIME,
                        'Sum-of-squares finalizer mismatch')
                finalizer_checks+=2
            for root in sums:
                trial=dict(inputs,t=root)
                require(interpret(system,trial,PRIME)[norm_port]==0,
                        'Encoded radical root failed')
                root_checks+=1
            # A relevant negative control: deleting the new tau weight must
            # change at least one checked finite-field norm polynomial.
            if not missing_tau_weight_detected:
                wrong_sums=branch_sums(prefix,PRIME,tau_weight=1)
                missing_tau_weight_detected=any(
                    product_value(prefix,wrong_sums,t,PRIME)
                    !=product_value(prefix,sums,t,PRIME) for t in range(17))
            signs['i_positive' if 2*inputs['i_raw']+1>0 else 'i_negative']+=1
            signs['T_positive' if inputs['T']>0 else 'T_negative' if inputs['T']<0 else 'T_zero']+=1
            signs['w_positive' if inputs['w_raw'] else 'w_zero']+=1
            fixture_counts[group]+=1
        require(fixture_counts[group]==16,'Insufficient split fixtures for '+group)
    require(missing_tau_weight_detected,'Missing-tau-weight negative control was ineffective')
    require(all(signs[key]>0 for key in signs),'Required sign/boundary coverage missing')

    mod4_checks=0
    for index in range(1024):
        if index<4:
            inputs={name:(0 if index==0 else 1 if index==1 else -1 if index==2
                          else (-1 if j%2 else 2)) for j,name in enumerate(RAW+FIXED)}
        else:
            inputs={name:rng.randint(-20,20) for name in RAW+FIXED}
        prefix=independent_prefix(inputs,4)
        values=interpret(system,inputs,4)
        compare_prefix(system,values,prefix,4)
        P=values[norm_port]
        require(P in (0,1),'Norm is not a square modulo four')
        require((1+P)%4!=3,'Product guard permits the negative unit modulo four')
        pv=interpret(product,inputs,4)[product['output']]
        sv=interpret(sos,inputs,4)[sos['output']]
        require(pv==(prefix['Nk']*prefix['Nt']*(1+P)-1)%4,
                'Product finalizer mismatch modulo four')
        require(sv==((prefix['Nk']-1)**2+(prefix['Nt']-1)**2+P*P)%4,
                'SOS finalizer mismatch modulo four')
        mod4_checks+=1

    report={
        'status':'PASS',
        'builder_sha256':hashlib.sha256(Path(builder.__file__).read_bytes()).hexdigest(),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'prime':PRIME,'seed':SEED,'variables':26,'ledgers':ledgers,
        'fixture_groups':fixture_counts,'search_attempts':attempts_by_group,
        'integer_input_sign_coverage':signs,
        'independent_prefix_formula_checks':prefix_checks+mod4_checks,
        'full_sixteen_branch_factorizations':sum(fixture_counts.values()),
        't_degree_upper_bound':16,
        'distinct_t_points_per_factorization':17,
        'factorization_point_checks':factor_checks,
        'encoded_branch_root_checks':root_checks,
        'finalizer_equality_checks_over_prime':finalizer_checks,
        'mod4_norm_and_finalizer_checks':mod4_checks,
        'missing_tau_weight_negative_control_detected':missing_tau_weight_detected,
        'validation_uses_explicit_exceptions':True,
        'scope':'Bounded exact algebra checks with synthetic coefficient ports. '
                'Zero-scale fixtures check algebra before the later integer soundness exclusion. '
                'No K215 halting witness, coefficient expansion, end-to-end formal proof, '
                'or new total-degree retest is claimed.'
    }
    args.receipt.parent.mkdir(parents=True,exist_ok=True)
    args.receipt.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
