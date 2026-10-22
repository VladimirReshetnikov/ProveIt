#!/usr/bin/env python3
"""Explicit fixed-marker transformation of three pinned ProveIt circuits.

Algebra/source checks only. Universality needs the mathematical fixed-marker
restoration argument and a valid fixed-program compiler export.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse
import json

REMOVE = {
    'scaled_t', 'odd_index', 'gamma_sum', 'index_product', 'index_rhs',
    'difference_multiple', 'exponent_partial', 'modulus_multiple',
    'exponent_rhs', 'mu2', 'kappa2', 'scaled_kappa2', 'norm_input',
}
VARIANTS = {
    'fixed_marker74': ('complete84_scaled_strong_output.json', 74, 157, [22,18,2,60,7,2,46]),
    'fixed_marker75': ('complete85_reduced_auxiliary_degree.json', 75, 125, [22,18,2,28,7,2,46]),
    'fixed_marker76': ('complete86_ordinary_auxiliary_projection.json', 76, 101, [22,18,2,28,7,2,22]),
    'fixed_marker82': ('complete92_norm_unit_guard.json', 82, 295, [22,18,2,7,2,244]),
}
FACTORS = ['norm_first','norm_main','norm_marker','norm_aux','norm_index','norm_transport','norm_strong']

def factors(name):
    return FACTORS if name != 'fixed_marker82' else ['norm_first','norm_main','norm_marker','norm_index','norm_transport','ng_unit']

def require(p, message):
    if not p:
        raise ValueError(message)

def circuit(parent, name):
    before = {r[0]: r for r in parent['source']}
    require(REMOVE <= set(before), 'missing input block')
    require(before['gamma_sum'] == ['gamma_sum','+','rho','sigma'], 'gamma source')
    require(before['scaled_t'] == ['scaled_t','*','twice_cell_bits','x'], 'input source')
    require(before['W'] == ['W','-','marked_rhs','Z'], 'marker source')
    ren = {'scaled_t':'twice_cell_bits','gamma_sum':'gamma','norm_input':'norm_marker'}
    rows=[]
    for row in parent['source']:
        if row[0] in REMOVE:
            continue
        rows.append([row[0],row[1]]+[ren.get(x,x) if isinstance(x,str) else x for x in row[2:]])
        if row[0] == 'W':
            rows.extend([
                ['marker_error','-','W','marker_constant'],
                ['marker_error_square','*','marker_error','marker_error'],
                ['norm_marker','+','marker_error_square',1],
            ])
    witnesses=[x for x in parent['witnesses'] if x not in ('delta','rho','sigma')]+['gamma']
    numerals=[x for x in parent['fixed_numerals'] if x != 'inner_bits']+['marker_constant']
    free=witnesses+numerals
    done=set(free)
    counts=Counter()
    for n, op, a, b in rows:
        require(n not in done,'duplicate output '+n)
        require(all(not isinstance(x,str) or x in done for x in (a,b)),'not scheduled '+n)
        done.add(n);counts[op]+=1
    seen=set()
    by_name={r[0]:r for r in rows}
    def visit(x):
        if not isinstance(x,str) or x in seen:
            return
        seen.add(x)
        if x in by_name:
            visit(by_name[x][2]);visit(by_name[x][3])
    visit(parent['output'])
    require(seen == set(free)|set(by_name),'dead or missing ports')
    spec=VARIANTS[name]
    require(len(rows)==spec[1] and len(witnesses)==(15 if name=='fixed_marker82' else 16),'ledger')
    return {'name':name,'source':rows,'output':parent['output'],'witnesses':witnesses,
            'fixed_numerals':numerals,'free':free,'domain':'strictly positive integer witnesses',
            'marker_recipe':'marker_constant = 2^inner_bits * (Bm1+1)^2; twice_cell_bits = 2*d, Bm1+1=2^d',
            'M':counts['*'],'A':counts['+']+counts['-'],'total':len(rows),
            'exact_degree':spec[2],'factor_exact_degrees':spec[3],'factors':factors(name)}

def evaluate(rows, values):
    e=dict(values)
    for n,op,a,b in rows:
        a=e[a] if isinstance(a,str) else a
        b=e[b] if isinstance(b,str) else b
        e[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return e

def add(a,b,p,sign=1):
    o=[0]*max(len(a),len(b))
    for i,v in enumerate(a):o[i]=v
    for i,v in enumerate(b):o[i]=(o[i]+sign*v)%p
    while len(o)>1 and o[-1]==0:o.pop()
    return o

def mul(a,b,p):
    o=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):o[i+j]=(o[i+j]+u*v)%p
    while len(o)>1 and o[-1]==0:o.pop()
    return o

def univariate(rows, values, p):
    e=deepcopy(values)
    for n,op,a,b in rows:
        a=e[a] if isinstance(a,str) else [a%p]
        b=e[b] if isinstance(b,str) else [b%p]
        e[n]=mul(a,b,p) if op=='*' else add(a,b,p,1 if op=='+' else -1)
    return e

def audit(root,out):
    results={}
    for name,(filename,count,degree,factor_degrees) in VARIANTS.items():
        raw=(root/filename).read_bytes();parent=json.loads(raw)['packet']
        child=circuit(parent,name)
        # Compare every retained register after evaluating the parent at x=1,
        # gamma=rho+sigma; only finalizer values and marker gate differ.
        checked=0
        for case in range(48):
            val={x:Fraction(((case+3)*(j+1))%23-11,(j%3)+1)
                 for j,x in enumerate(parent['free'])}
            val['x']=1
            old=evaluate(parent['source'],val)
            nv={x:val[x] for x in child['free'] if x not in ('gamma','marker_constant')}
            nv.update(gamma=val['rho']+val['sigma'],marker_constant=7)
            new=evaluate(child['source'],nv)
            final={'norm_triple','norm_four','norm_product','all_units','seven_units','ng_P5a','ng_P5','ng_product',parent['output']}
            for k in set(old)&set(new)-final:
                require(old[k]==new[k],'retained value '+k);checked+=1
            # At the factor cut, the old input norm has been replaced by M.
            prod=Fraction(1)
            for f in factors(name):prod*=new[f]
            target=new['A'] if name not in ('fixed_marker76','fixed_marker82') else 1
            require(new[child['output']]==prod-target,'whole finalizer')
        diags=[]
        for B,p in ((16,1000000007),(32,1000000009)):
            constants=dict(Bm1=B-1,Kconstant=3,twice_cell_bits=2,MC=5,MF=7,marker_constant=2*B*B)
            val={x:[constants[x]] if x in constants else [0,1] for x in child['free']}
            uni=univariate(child['source'],val,p)
            got=[len(uni[f])-1 for f in factors(name)]
            require(got==factor_degrees,(name,got,factor_degrees))
            require(len(uni[child['output']])-1==degree,'degree attained')
            diags.append({'B':B,'modulus':p,'degree':degree,'factor_degrees':got,
                          'leading_coefficient':uni[child['output']][-1],
                          'coefficients_sha256':sha256(json.dumps(uni[child['output']]).encode()).hexdigest()})
        child['parent_sha256']=sha256(raw).hexdigest()
        child['parent_file']=filename
        child['retained_register_evaluations']=checked
        child['dense_degree_checks']=diags
        child['scope']='Source algebra and degree diagnostics; mathematical marker restoration and compiler theorem are separate.'
        results[name]=child
    (out/'fixed_marker_variants.json').write_text(json.dumps(results,indent=2,sort_keys=True)+'\n')
    systems={}
    for name in ('fixed_marker74','fixed_marker76','fixed_marker82'):
        p=results[name]
        comparisons=[[f,1] for f in ('norm_first','norm_main','norm_index','norm_transport')]
        if name=='fixed_marker82':
            comparisons += [['ng_A2','ng_four'],['W','marker_constant']]
        elif name=='fixed_marker76':
            comparisons += [['norm_aux',1],['ic22','R16'],['W','marker_constant']]
        else:
            comparisons += [['norm_aux',1],['norm_strong','A' if name=='fixed_marker74' else 1],['W','marker_constant']]
        needed=set()
        by_name={r[0]:r for r in p['source']}
        def live(x):
            if not isinstance(x,str) or x in needed:return
            needed.add(x)
            if x in by_name:
                live(by_name[x][2]);live(by_name[x][3])
        for lhs,rhs in comparisons:live(lhs);live(rhs)
        rows=[r for r in p['source'] if r[0] in needed]
        counts=Counter(r[1] for r in rows)
        systems[name+'_system']={'source':rows,'comparisons':comparisons,'witnesses':p['witnesses'],
            'fixed_numerals':p['fixed_numerals'],'free':p['free'],'M':counts['*'],'A':counts['+']+counts['-'],
            'total':len(rows),'equations':len(comparisons),'domain':p['domain'],
            'max_residual_degree':60 if name=='fixed_marker74' else 28 if name=='fixed_marker76' else 244}
        if name=='fixed_marker76':
            sos=deepcopy(rows)
            squares=[]
            for j,(lhs,rhs) in enumerate(comparisons):
                sos.append([f'residual_{j}','-',lhs,rhs])
                sos.append([f'square_{j}','*',f'residual_{j}',f'residual_{j}'])
                squares.append(f'square_{j}')
            last=squares[0]
            for j,sq in enumerate(squares[1:],1):
                sos.append([f'sum_{j}','+',last,sq]);last=f'sum_{j}'
            sc=Counter(r[1] for r in sos)
            systems[name+'_sos']={'source':sos,'output':last,'witnesses':p['witnesses'],
                'fixed_numerals':p['fixed_numerals'],'free':p['free'],'M':sc['*'],'A':sc['+']+sc['-'],
                'total':len(sos),'domain':p['domain'],'exact_degree':56,
                'leading_form':'(eta+zeta)^4*w^4*s^8*(Bm1*Jrep)^28*auxiliary_quotient^4*f^8'}
    (out/'fixed_marker_systems.json').write_text(json.dumps(systems,indent=2,sort_keys=True)+'\n')
    return {k:{x:v[x] for x in ('M','A','total','exact_degree')} for k,v in results.items()}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True);print(json.dumps(audit(a.root,a.out),sort_keys=True))
