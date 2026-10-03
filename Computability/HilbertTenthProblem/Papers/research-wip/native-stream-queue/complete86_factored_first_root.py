#!/usr/bin/env python3
"""A five-gate ordinary first norm in the complete asymmetric universal sources.

Reads authenticated source/receipt bytes only; no historical module imports.
The positive-zero coordinate proof is in the companion mathematical note.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path
import random
import sympy as sp

PINS = {
    'complete75_asymmetric_scale_tradeoffs.py': 'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660',
    'complete75_asymmetric_scale_tradeoffs.json': '47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98',
    'complete75_normalized_strong87.py': '7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8',
    'complete75_coupled_index_linear88.py': 'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed',
    'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
}
OLD_WITNESSES = ['Jrep','F','alpha','zplus','f','h','i','j','o','s','w',
                 'tau_gap','eta','zeta','y_aux','Z','delta','rho','sigma']
WITNESSES = ['tau_root' if n == 'tau_gap' else n for n in OLD_WITNESSES]
CONSTANTS = ['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS = ['norm_first','norm_main','norm_input','norm_aux','norm_index',
           'norm_transport','norm_strong','norm_linear']
OLD_BLOCK = {
    'tau_square': ['*','tau_gap','tau_gap'],
    'first_root_base': ['*','UM','ksn2'],
    'twice_tau_gap': ['+','tau_gap','tau_gap'],
    'first_signed_gap': ['-','twice_tau_gap','R10b'],
    'first_cross': ['*','first_root_base','first_signed_gap'],
    'norm_first': ['+','tau_square','first_cross'],
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def parents(root):
    root = Path(root)
    for name, pin in PINS.items():
        need(sha((root / name).read_bytes()) == pin, 'Pinned parent ' + name)
    records = json.loads((root / 'complete75_asymmetric_scale_tradeoffs.json').read_text())['source']
    need([r['normalized'] for r in records] == [True, False], 'Both complete parent modes')
    return records


def rewrite(root, normalized=True, supplied=None):
    need(type(normalized) is bool, 'Exact Boolean mode')
    record = parents(root)[0 if normalized else 1]
    old = record['source']
    if supplied is not None:
        need(exact(supplied, old), 'Only the complete canonical selected parent')
    nodes = {n: [op,a,b] for n,op,a,b in old}
    need(all(nodes[n] == row for n,row in OLD_BLOCK.items()), 'Literal six-gate first norm')
    uses = {n for n,op,a,b in old if 'tau_gap' in (a,b)}
    need(uses == {'tau_square','twice_tau_gap'}, 'First-root coordinate is private')
    need('first_next' not in nodes and 'first_product' not in nodes, 'Fresh registers')
    new = []
    for n,op,a,b in old:
        if n == 'tau_square':
            new.append([n,'*','tau_root','tau_root'])
        elif n == 'norm_first':
            new += [['first_next','+','first_root_base','R10b'],
                    ['first_product','*','first_root_base','first_next'],
                    ['norm_first','-','tau_square','first_product']]
        elif n not in ('twice_tau_gap','first_signed_gap','first_cross'):
            new.append([n,op,a,b])
    return old, new


def evaluate(rows, values):
    env = dict(values)
    for name, op, a, b in rows:
        a = a if type(a) is int else env[a]
        b = b if type(b) is int else env[b]
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def inspect(rows, witnesses):
    free = set(witnesses + ['x'] + CONSTANTS)
    available = set(free)
    deps, counts = {}, Counter()
    for name,op,a,b in rows:
        need(type(name) is str and name not in available and op in ('+','-','*'), 'Fresh legal gate')
        for v in (a,b):
            need(type(v) is int or (type(v) is str and v in available), 'Exact closed operand')
        deps[name] = [v for v in (a,b) if type(v) is str and v in deps]
        available.add(name)
        counts[op] += 1
    used_free = {v for _,_,a,b in rows for v in (a,b) if type(v) is str and v in free}
    need(used_free == free, 'Exactly the paid input/fixed-numeral/witness interface')
    live = set()
    def visit(n):
        if n in deps and n not in live:
            live.add(n)
            for d in deps[n]:
                visit(d)
    visit('polynomial')
    need(live == set(deps), 'Every counted gate live')
    need(rows[-1] == ['polynomial','-','eight_units',1], 'Final subtraction is paid')
    return dict(operations=len(rows), M=counts['*'], A=counts['+']+counts['-'],
                certificate_operations=len(rows)-1, comparisons=1,
                positive_witnesses=len(witnesses), all_gates_live=True,
                fixed_numerals=CONSTANTS, ordinary_input='x')


def structural_proof(old, new):
    def forms(rows):
        env = {}
        for n,op,a,b in rows:
            if n == 'norm_first':
                env[n] = ('proved_first_norm_coordinate_identity',)
                continue
            aa = ('integer',a) if type(a) is int else env.get(a,('free',a))
            bb = ('integer',b) if type(b) is int else env.get(b,('free',b))
            env[n] = (op,aa,bb)
        return env
    a,b = forms(old),forms(new)
    for n in FACTORS + ['polynomial']:
        need(a[n] == b[n], 'Full expression-DAG proof after first-factor identity: ' + n)
    return len(FACTORS) + 1


def dense(rows, values, prime):
    def plus(a,b,sign=1):
        out = [((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime
               for i in range(max(len(a),len(b)))]
        while len(out)>1 and out[-1]==0:
            out.pop()
        return out
    def times(a,b):
        out = [0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                out[i+j] = (out[i+j]+x*y)%prime
        while len(out)>1 and out[-1]==0:
            out.pop()
        return out
    env = dict(values)
    for n,op,a,b in rows:
        a = [a%prime] if type(a) is int else env[a]
        b = [b%prime] if type(b) is int else env[b]
        env[n] = times(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1)
    return env


def components():
    cases=[]
    for V in (1,2,5,16,127):
        T,k=1,0
        for index in range(1,8):
            T,k=(2*V+1)*T+2*V*(V+1)*k,2*T+(2*V+1)*k
            L=V*k
            g=T-L
            need(T*T-L*(L+k)==1 and g>0 and g*g+L*(2*g-k)==1, 'Actual Pell component')
            cases.append(dict(V=V,index=index,T=T,k=k,L=L,g=g))
    unit_cases=[]
    for L in range(1,129):
        for k in range(2,65):
            for sign in (-1,1):
                value=L*L+L*k+sign
                T=isqrt(value)
                if T*T != value:
                    continue
                need(L*k+sign>0 and T>L and T-L>0, 'Both unit signs give positive inverse')
                unit_cases.append(dict(L=L,k=k,sign=sign,T=T,g=T-L))
    need({r['sign'] for r in unit_cases} == {-1,1}, 'Both local unit signs tested')
    return dict(Pell_component_count=len(cases),Pell_components=cases,
                inverse_unit_count=len(unit_cases),inverse_unit_cases=unit_cases)


def verify(root):
    T,L,k,g=sp.symbols('T L k g')
    ordinary=T*T-L*(L+k)
    shifted=g*g+L*(2*g-k)
    need(sp.expand(ordinary.subs(T,L+g)-shifted)==0, 'Forward local polynomial identity')
    need(sp.expand(shifted.subs(g,T-L)-ordinary)==0, 'Inverse local polynomial identity')
    rng=random.Random(861792026)
    records=[]
    counts=Counter(local_symbolic_coordinate_identities=2)
    for normalized in (True,False):
        old,new=rewrite(root,normalized)
        baseline=inspect(old,OLD_WITNESSES)
        ledger=inspect(new,WITNESSES)
        need((baseline['operations'],ledger['operations'],ledger['M'],ledger['A']) ==
             ((87,86,48,38) if normalized else (88,87,47,40)), 'Complete operation improvement')
        counts['complete_factor_and_finalizer_DAG_identities'] += structural_proof(old,new)
        # Full all-value coordinate maps, including signed/rational off-zero tuples.
        for index in range(256):
            domain=index%4
            values={n:(rng.randrange(1,6) if domain==0 else rng.randrange(-4,5)) for n in OLD_WITNESSES+['x']}
            if domain==3:
                values={n:Fraction(v,rng.randrange(1,5)) for n,v in values.items()}
            B=(16,32,64,128)[index%4]
            fixed=dict(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3)
            values.update(fixed)
            before=evaluate(old,values)
            image={n:v for n,v in values.items() if n!='tau_gap'}
            image['tau_root']=before['first_root_base']+values['tau_gap']
            after=evaluate(new,image)
            need(all(before[f]==after[f] for f in FACTORS+['polynomial']), 'Every factor and whole forward coordinate identity')
            need(image['tau_root']-after['first_root_base']==values['tau_gap'], 'Exact coordinate inverse')
            counts['full_forward_coordinate_identities']+=1
            counts['rational_forward_cases']+=domain==3
            counts['signed_integer_forward_cases']+=domain in (1,2)
            if domain==0:
                need(min(image.values())>0, 'Forward map preserves whole positive orthant')
                counts['whole_positive_forward_maps']+=1
            # Start independently on the new side; its off-zero inverse need not be positive.
            child={('tau_root' if n=='tau_gap' else n):v for n,v in values.items()}
            got=evaluate(new,child)
            back={n:v for n,v in child.items() if n!='tau_root'}
            back['tau_gap']=child['tau_root']-got['first_root_base']
            pulled=evaluate(old,back)
            need(all(got[f]==pulled[f] for f in FACTORS+['polynomial']), 'Every factor and whole inverse coordinate identity')
            need(back['tau_gap']+pulled['first_root_base']==child['tau_root'], 'Inverse-forward roundtrip')
            counts['full_inverse_coordinate_identities']+=1
        degree_cases=[]
        for B,prime in ((16,1009),(32,1013),(64,1019)):
            env={n:[j+1,2*j+3] for j,n in enumerate(WITNESSES+['x'])}
            env.update({n:[v] for n,v in dict(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3).items()})
            polynomials=dense(new,env,prime)
            wanted=[22,18,32,56 if normalized else 24,7,3,34 if normalized else 22,7]
            degrees=[len(polynomials[f])-1 for f in FACTORS]
            need(degrees==wanted, 'Every exact factor degree attained')
            top={n:v[1] for n,v in env.items() if len(v)==2}
            Q=(B-1)*top['Jrep'];kk=top['eta']+top['zeta'];gamma=top['rho']+top['sigma']
            C=Q-top['F']-top['Z']-top['alpha']-env['twice_cell_bits'][0]*top['x']
            if normalized:
                leading=-32*Q**108*top['h']**2*gamma*top['delta']**2*top['i']**4*kk**13*top['w']**18*top['s']**30*C
            else:
                leading=32*Q**80*top['h']**2*gamma*top['delta']**2*top['i']**2*top['f']**2*kk**9*top['w']**14*top['s']**22*C
            poly=polynomials['polynomial']
            need(len(poly)-1==sum(wanted) and poly[-1]==leading%prime and poly[-1]!=0, 'Exact complete leading form attained')
            degree_cases.append(dict(B=B,prime=prime,factor_degrees=degrees,degree=len(poly)-1,
                                     leading_coefficient=poly[-1],all_coefficients_sha256=sha(json.dumps(poly).encode())))
            counts['complete_dense_degree_and_leading_checks']+=1
        for bad in (old[:-1],old+[['extra','+',1,1]],json.loads(json.dumps(new))):
            try:
                rewrite(root,normalized,bad)
            except ValueError:
                counts['wrong_complete_parent_rejections']+=1
            else:
                raise ValueError('Noncanonical complete parent accepted')
        boundary={n:1 for n in WITNESSES+['x']}
        boundary.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19)
        evaluated=evaluate(new,boundary)
        restored=boundary['tau_root']-evaluated['first_root_base']
        need(restored<0 and evaluated['polynomial']!=0, 'Explicit off-zero positive-domain boundary')
        ledger.update(exact_degree=179 if normalized else 135,factor_degrees=[22,18,32,56 if normalized else 24,7,3,34 if normalized else 22,7])
        records.append(dict(normalized=normalized,baseline=baseline,ledger=ledger,source=new,
                            output='polynomial',witnesses=WITNESSES,degree_checks=degree_cases,
                            positive_offzero_inverse_counterexample=dict(assignment=boundary,restored_gap=restored,complete_output=evaluated['polynomial'])))
    return dict(status='PASS_COMPLETE86_AND87',source_sha256=sha(Path(__file__).read_bytes()),
                parent_pins=PINS,forms=records,counts=dict(counts),components=components(),
                scope='Complete fixed-program universal parent sources and full positive-zero bijection under first-root coordinate change. No ratio/strong/input condition removed; no materialized astronomical universal Pell zero, unrestricted optimum or Lean proof.')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--expect',type=Path)
    args=parser.parse_args()
    result=verify(args.root)
    if args.expect:
        need(exact(result,json.loads(args.expect.read_text())), 'Typed saved receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],counts=result['counts'],ledgers=[r['ledger'] for r in result['forms']]),indent=2))
