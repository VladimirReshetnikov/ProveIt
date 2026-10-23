#!/usr/bin/env python3
"""Emit and audit the 24-integer signed-saturation specialization.

The core circuit and norm oracle are inherited, with attribution, from
ProveIt package 21 at a477d0fc8b6feda53796835564a988015e744d4d.
The six-positive-coordinate theorem is new; see PROOF24.md / report.tex.
This program verifies finite arithmetic, not the machine/compiler theorem.
Only the Python standard library is used. Checks remain active under -O.
"""
from collections import Counter
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('inherited_norm12', HERE/'upstream'/'build_norm12.py')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
GUARDED = ['J', 'F', 'alpha', 'z', 'eta', 'zeta']
FIXED = ['beta', 'K0', 'MC', 'MF']


def require(condition, description):
    if not condition:
        raise ValueError(description)


def lift(source):
    p = deepcopy(source)
    prefix, witnesses = [], []
    for n in GUARDED:
        x, y, t = n+'_x', n+'_y', n+'_t'
        witnesses += [x, y, t]
        prefix += [[n+'_x2','*',x,x], [n+'_y2','*',y,y],
                   [n+'_tp1','+',t,1], [n+'_pronic','*',t,n+'_tp1'],
                   [n+'_sum0','+',n+'_x2',n+'_y2'],
                   [n+'_sum1','+',n+'_sum0',n+'_pronic'],
                   [n,'+',n+'_sum1',1]]
    witnesses += ['i0','s0','w0','h','T','r']
    prefix += [['twice_i0','*',2,'i0'], ['i','+','twice_i0',1],
               ['twice_s0','*',2,'s0'], ['s','+','twice_s0',1],
               ['w','*','w0','w0']]
    suffix = source['name'].removeprefix('norm12_')
    p.update(name='integer24_'+suffix, witnesses=witnesses,
             domain='unrestricted integers', source=prefix+p['source'],
             coefficient_binding='../coefficients/COEFFICIENT_BINDING.json',
             proof='../report.tex, signed saturation theorem')
    p.pop('ledger', None)
    if suffix == 'system':
        p['residual_exact_degrees'] = [12,4,2416]
    else:
        p['exact_degree'] = 2432 if suffix == 'product' else 4832
    return p


def evaluate(p, values, modulus=None):
    vals = dict(values)
    for n, op, left, right in p['source']:
        a = left if isinstance(left,int) else vals[left]
        b = right if isinstance(right,int) else vals[right]
        c = a+b if op=='+' else a-b if op=='-' else a*b
        vals[n] = c if modulus is None else c % modulus
    return vals


def shifted_system(p):
    """The inherited z_old=z+1 shift, plus a free final comparison."""
    p=deepcopy(p)
    p.update(name='integer24_system_shifted',
             coordinate_relation='z_old=z+1; each unshifted zero has z_old>=2 after compiler recovery.')
    p['source']=[row for row in p['source'] if row[0] not in ['trans1','Nt','N']]
    at=next(i for i,row in enumerate(p['source']) if row[0]=='trans2')+1
    p['source'].insert(at,['transport_rhs','+','F','trans2'])
    p['comparisons']=[['Nk',1],['trans0','transport_rhs'],['N00','GN11']]
    p.pop('ledger',None)
    return p


def structural_audit(p):
    known = set(p['witnesses']+p['fixed_numerals'])
    degree = {n:1 for n in p['witnesses']}
    degree.update({n:0 for n in p['fixed_numerals']})
    for n,op,a,b in p['source']:
        require(n not in known and op in ['+','-','*'], 'invalid or duplicate gate '+n)
        require(all(isinstance(v,int) or v in known for v in [a,b]), 'undefined operand '+n)
        da = 0 if isinstance(a,int) else degree[a]
        db = 0 if isinstance(b,int) else degree[b]
        degree[n] = da+db if op=='*' else max(da,db)
        known.add(n)
    outputs = [p['output']] if 'output' in p else [x for pair in p['comparisons'] for x in pair if isinstance(x,str)]
    live = set(outputs)
    for n,op,a,b in reversed(p['source']):
        if n in live:
            live.update(v for v in [a,b] if isinstance(v,str))
    require(all(n in live for n,_,_,_ in p['source']), 'dead gate')
    require(set(p['witnesses']+p['fixed_numerals']) <= live, 'unused port')
    require(len(p['witnesses']) == len(set(p['witnesses'])) == 24, 'variable count')
    count = Counter(row[1] for row in p['source'])
    p['ledger'] = dict(unknowns=24, operations=len(p['source']),
                       multiplications=count['*'], additions_subtractions=count['+']+count['-'],
                       all_gates_live=True, all_ports_live=True,
                       syntactic_degree_upper_bounds={n:degree[n] for n in outputs})
    return degree


def recover_core(vals):
    result = {n:1+vals[n+'_x']**2+vals[n+'_y']**2+vals[n+'_t']*(vals[n+'_t']+1) for n in GUARDED}
    result.update(i=2*vals['i0']+1, s=2*vals['s0']+1, w=vals['w0']**2,
                  h=vals['h'], T=vals['T'], r=vals['r'])
    result.update({n:vals[n] for n in FIXED})
    return result


def audit(circuits, parents):
    rng = random.Random(2420261022)
    for _ in range(32):
        vals = {n:rng.randrange(-3,4) for n in circuits[0]['witnesses']+FIXED}
        core = recover_core(vals)
        a = evaluate(circuits[0], vals)
        require(a['N'] == BASE.independent_norm(a), 'eight-conjugate norm identity')
        require(a['N1'] % 8 == 0 and (a['N']-a['N0']**2) % 64 == 0, 'unit guard parity')
        for c,p in zip(circuits,parents):
            x,y = evaluate(c,vals), evaluate(p,core)
            outputs = [c['output']] if 'output' in c else ['Nk','Nt','N']
            require(all(x[o] == y[o] for o in outputs), 'substitution identity')

    # Small masks meeting the stated low-bit/popcount hypotheses. These are
    # diagnostic values only, never the instance's fixed four coefficients.
    # B=32, native MC=10, native MF=28, shifted MF=59.
    signed_cases = 0
    for w0 in [0,1,2]:
      for s0 in [-3,-1,0,2]:
       for T in [-2,0,3]:
        core = dict(J=1,F=2,alpha=3,z=1,eta=1,zeta=2,
                    i=-3,s=2*s0+1,w=w0*w0,h=-2,T=T,r=-1,
                    beta=31,K0=127,MC=10,MF=59)
        a = evaluate(parents[0],core)
        Z,aa,cc = abs(a['Y']),abs(a['a']),abs(a['c'])
        require(a['Delta'] > a['q']**4 > a['R'] > 0, 'signed Delta bound')
        require(a['D'] > a['Delta']+cc and 1<a['b']<a['Q'], 'b/Q interval')
        require(a['Bnd'] > 0 and abs(a['H'])*a['Bnd'] > 2, 'signed weight')
        require(a['L'] % abs(a['H']) == 1, 'main-root congruence')
        if w0:
            require(a['k']*Z*(2*aa-7)>2, 'strict root-separation lower bound')
        else:
            require(a['A']==1, 'zero-scale degenerate first root')
        signed_cases += 1

    # Leading-homogeneous evaluations corroborate, but do not replace, the
    # exact symbolic leading forms proved in the manuscript.
    leading = []
    for prime in [1000000007,1000000009]:
        vals = {n:(1,rng.randrange(1,prime)) for n in circuits[1]['witnesses']}
        vals.update({n:(0,x) for n,x in zip(FIXED,[31,127,10,59])})
        for n,op,l,r in circuits[1]['source']:
            dl,cl = (0,l%prime) if isinstance(l,int) else vals[l]
            dr,cr = (0,r%prime) if isinstance(r,int) else vals[r]
            if op=='*':
                vals[n]=(dl+dr,cl*cr%prime)
            else:
                d=max(dl,dr)
                v=(cl if dl==d else 0)+(1 if op=='+' else -1)*(cr if dr==d else 0)
                vals[n]=(d,v%prime)
        require(vals['polynomial'][0]==2432 and vals['polynomial'][1]!=0, 'leading degree')
        leading.append(dict(prime=prime,degree=vals['polynomial'][0],leading_value=vals['polynomial'][1]))
    return dict(exact_norm_and_substitution_fixtures=32, signed_boundary_fixtures=signed_cases,
                leading_form_modular_diagnostics=leading,
                symbolic_product_coefficient='2^353 * beta^853',
                symbolic_product_monomial='J_x^1706*h*z_x^2*i0^48*eta_x^224*w0^226*s0^225',
                scope='Finite algebra and domain-bound diagnostics only; no decision of solvability and no end-to-end formal compiler check.')


def main():
    parents = BASE.construct()
    circuits = [lift(p) for p in parents]
    for p,ops,deg in zip(circuits,[159,163,166],[2416,2432,4832]):
        d=structural_audit(p)
        require(len(p['source'])==ops,'operation count')
        require(d[p.get('output','N')]==deg,'degree upper bound')
    checks=audit(circuits,parents)
    shifted=shifted_system(circuits[0])
    degrees=structural_audit(shifted)
    require(len(shifted['source'])==157,'shifted operation count')
    require(degrees['N00']==2416,'shifted degree')
    rng=random.Random(24157)
    for _ in range(32):
        vals={n:rng.randrange(-3,4) for n in shifted['witnesses']+FIXED}
        new=evaluate(shifted,vals)
        old_core=recover_core(vals)
        old_core['z']+=1
        old=evaluate(parents[0],old_core)
        require(old['Nt']-1==new['trans0']-new['transport_rhs'],'shifted transport identity')
        require(old['N']==new['N00']-new['GN11'],'direct norm comparison')
    checks['shifted_system_exact_fixtures']=32
    circuits.append(shifted)
    for p in circuits:
        (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    receipt=dict(source_commit='a477d0fc8b6feda53796835564a988015e744d4d',
                 packets=[dict(name=p['name'],ledger=p['ledger'],
                               exact_degree=p.get('exact_degree'),
                               residual_exact_degrees=p.get('residual_exact_degrees')) for p in circuits],
                 checks=checks)
    (HERE/'CHECKS24.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()
