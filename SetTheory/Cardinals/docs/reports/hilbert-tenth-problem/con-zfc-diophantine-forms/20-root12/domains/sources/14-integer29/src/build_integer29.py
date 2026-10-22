#!/usr/bin/env python3
"""Emit and audit exact 29-integer substitutions of the ordinary certificate.

This verifies circuit algebra, finite specialization degrees, and counts.
The universal solvability argument is in the accompanying mathematical notes.
"""
import argparse
import copy
import json
import random
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'data'
NORMALIZED = HERE.parent / 'vendor' / 'blank67'
POSITIVE = ['Jrep', 'F', 'alpha', 'transport_quotient', 's', 'eta', 'zeta']
FREE = ['f', 'h', 'auxiliary_quotient', 'tau_root', 'y_aux', 'gamma']
CASES = [
    ('ordinary', 'blank_ordinary_poly69', 'blank_ordinary_integer29_poly121', 121, 188),
    ('ordinary', 'blank_ordinary_system61', 'blank_ordinary_integer29_system113', 113, 50),
    ('ordinary', 'blank_ordinary_sos78', 'blank_ordinary_integer29_sos130', 130, 100),
    ('normalized', 'fixed_blank_67', 'blank_normalized_integer29_poly119', 119, 300),
    ('normalized', 'fixed_blank_68', 'blank_normalized_integer29_poly120', 120, 236),
]

def ledger(source):
    cnt = Counter(row[1] for row in source)
    return dict(operations=len(source), M=cnt['*'], A=cnt['+']+cnt['-'])

def substitution():
    source, names = [], []
    for v in POSITIVE:
        u, t, r = (v+'__'+s for s in ('u', 'v', 'r'))
        names.extend([u, t, r])
        source.extend([
            [v+'__u2', '*', u, u],
            [v+'__v2', '*', t, t],
            [v+'__rp1', '+', r, 1],
            [v+'__tri', '*', r, v+'__rp1'],
            [v+'__two_sq', '+', v+'__u2', v+'__v2'],
            [v+'__nonnegative', '+', v+'__two_sq', v+'__tri'],
            [v, '+', v+'__nonnegative', 1],
        ])
    names.extend(FREE+['i_integer', 'w_integer'])
    source.extend([
        ['i__twice', '*', 2, 'i_integer'],
        ['i', '+', 'i__twice', 1],
        ['w', '*', 'w_integer', 'w_integer'],
    ])
    assert len(source) == 52 and len(names) == 29
    return source, names

def evaluate(packet, values):
    values = dict(values)
    for name, op, a, b in packet['source']:
        x = a if isinstance(a, int) else values[a]
        y = b if isinstance(b, int) else values[b]
        assert name not in values
        values[name] = x+y if op=='+' else x-y if op=='-' else x*y
    return values

def transformed(values):
    ans = {name: values[name] for name in FREE}
    for v in POSITIVE:
        u,t,r = (values[v+'__'+s] for s in ('u','v','r'))
        ans[v] = 1+u*u+t*t+r*(r+1)
        assert ans[v] > 0
    ans['i'] = 2*values['i_integer']+1
    ans['w'] = values['w_integer']**2
    assert ans['i'] != 0 and ans['w'] >= 0
    return ans

def padd(a,b,sign=1):
    c = [0]*max(len(a),len(b))
    for j,x in enumerate(a): c[j] += x
    for j,x in enumerate(b): c[j] += sign*x
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def pmul(a,b):
    c = [0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b): c[j+k] += x*y
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def polynomial_specialization(packet, beta=15):
    """All positive triples are (t,0,0); other witnesses equal t."""
    env = {name:[0,1] for name in packet['witnesses']}
    for v in POSITIVE:
        env[v+'__v']=[0]
        env[v+'__r']=[0]
    env.update(Bm1=[beta], Kconstant=[19], MC=[2], MF=[20])
    for name,op,a,b in packet['source']:
        x=[a] if isinstance(a,int) else env[a]
        y=[b] if isinstance(b,int) else env[b]
        env[name]=pmul(x,y) if op=='*' else padd(x,y,1 if op=='+' else -1)
    return env

def weighted_upper_bounds(base):
    """Ring identity removes the known cancellation in the main norm.

    N1=2ac(X+gamma H)+(X+gamma H)^2-Hc^2.
    All other additions/subtractions use the conservative maximum bound.
    """
    env={name:2 if name in POSITIVE+['w'] else 1 for name in base['witnesses']}
    env.update({name:0 for name in base['fixed_numerals']})
    for name,op,a,b in base['source']:
        x=0 if isinstance(a,int) else env[a]
        y=0 if isinstance(b,int) else env[b]
        env[name]=x+y if op=='*' else max(x,y)
        if name=='norm_main':
            r=max(env['wn2'],env['gamma']+env['a4m5'])
            env[name]=max(env['R12']+env['R10a']+r,2*r,
                          env['a4m5']+env['c2'])
    return env

def outputs(packet):
    if 'output' in packet: return [packet['output']]
    names=[]
    for lhs,rhs in packet['comparisons']:
        if isinstance(lhs,str): names.append(lhs)
        if isinstance(rhs,str): names.append(rhs)
    return names

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--ordinary-dir',type=Path,default=PARENT)
    ap.add_argument('--normalized-dir',type=Path,default=NORMALIZED)
    ap.add_argument('--output-dir',type=Path,default=PARENT)
    args=ap.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    rng=random.Random(20261022)
    prelude, names=substitution()
    receipts=[]
    for kind,srcname,outname,count,degree in CASES:
        basedir=args.ordinary_dir if kind=='ordinary' else args.normalized_dir
        base=json.loads((basedir/(srcname+'.json')).read_text())
        base=base.get('packet',base)
        keep=['fixed_numerals','witnesses','source','output','comparisons','factors',
              'factor_exact_degrees','residual_exact_degrees']
        out={key:copy.deepcopy(base[key]) for key in keep if key in base}
        out['name']=outname
        out['witness_domain']='unrestricted integers'
        out['witnesses']=names
        out['source']=prelude+base['source']
        out['ledger']=ledger(out['source'])
        out['exact_degree' if 'output' in base else 'max_equation_degree']=degree
        out['substitution']={
            'positive_ports':POSITIVE,
            'positive_formula':'1+u^2+v^2+r(r+1)',
            'free_ports':FREE,
            'i':'2*i_integer+1',
            'w':'w_integer^2',
            'added_operations':ledger(prelude),
        }
        factor_degrees=([44,35,50,13,4,42] if kind=='ordinary' else
                        [44,35,114 if srcname.endswith('67') else 50,13,4,90])
        if 'factor_exact_degrees' in out:
            out['factor_exact_degrees']=factor_degrees
        if 'residual_exact_degrees' in out:
            out['residual_exact_degrees']=[44,35,50,13,4,42]
        assert out['ledger']['operations']==count
        for _ in range(100):
            vv={name:rng.randrange(-4,5) for name in names}
            fixed=dict(Bm1=15,Kconstant=19,MC=2,MF=20)
            b=evaluate(base,{**fixed,**transformed(vv)})
            n=evaluate(out,{**fixed,**vv})
            assert all(b[name]==n[name] for name in outputs(base))
            a=n['R12']; c=n['R10a']; x=n['wn2']; gam=n['gamma']; H=n['a4m5']
            r=x+gam*H
            assert n['norm_main']==2*a*c*r+r*r-H*c*c
        specialized=polynomial_specialization(out)
        upper=weighted_upper_bounds(base)
        if 'output' in base:
            deg=len(specialized[base['output']])-1
            assert deg==degree==upper[base['output']]
            lead=specialized[base['output']][-1]
            if kind=='ordinary':
                expected=-32768*15**55 if 'poly' in outname else 16*15**28
            else:
                expected=2097152*15**91 if srcname.endswith('67') else 32768*15**71
            assert lead==expected
        else:
            equation_degrees=[]
            for lhs,rhs in base['comparisons']:
                a=[lhs] if isinstance(lhs,int) else specialized[lhs]
                b=[rhs] if isinstance(rhs,int) else specialized[rhs]
                equation_degrees.append(len(padd(a,b,-1))-1)
            assert equation_degrees==[44,35,50,13,4,42]
            assert max(equation_degrees)==degree
            lead=None
        (args.output_dir/(outname+'.json')).write_text(json.dumps(out,indent=2)+'\n')
        receipts.append(dict(name=outname,witnesses=len(names),ledger=out['ledger'],
            degree=degree,random_exact_substitution_checks=100,
            degree_method='weighted upper bound plus exact univariate specialization',
            main_norm_identity_checked=True,
            specialized_leading_coefficient=lead))
    (args.output_dir/'integer29_verification.json').write_text(json.dumps(receipts,indent=2)+'\n')
    print(json.dumps(receipts,indent=2))

if __name__=='__main__': main()

