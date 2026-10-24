#!/usr/bin/env python3
"""Exact coordinated-variable reductions beyond the inspected incoming family."""
from pathlib import Path
import hashlib
import json
from polynomial import Poly, parse, require
from build_family import verify_coefficients, verify_source_pins, PORTS

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'equations'


def square_coefficient(poly, wanted, variables):
    """Extract one SOS coefficient without expanding irrelevant monomials."""
    variables=set(variables)
    groups={}
    for monomial,coefficient in poly.terms.items():
        vp={v:e for v,e in monomial if v in variables}
        if any(e>wanted.get(v,0) for v,e in vp.items()):
            continue
        key=tuple(sorted(vp.items()))
        fixed=tuple((v,e) for v,e in monomial if v not in variables)
        groups[key]=groups.get(key,Poly.integer(0))+Poly({fixed:coefficient})
    out=Poly.integer(0)
    for key,part in groups.items():
        powers=dict(key)
        complement=tuple(sorted((v,e-powers.get(v,0)) for v,e in wanted.items() if e-powers.get(v,0)))
        out=out+part*groups.get(complement,Poly.integer(0))
    return out


def emit(name,variables,rows,expected_degree,wanted,coefficient,restorations,compact=None):
    live=set().union(*(p.symbols() for p in rows))
    require(live<=set(variables+PORTS),name+' unbound symbols')
    require(set(variables)<=live,name+' dead variables')
    ds=[p.degree(variables) for p in rows]
    require(2*max(ds)==expected_degree,name+' degree upper bound')
    exact=sum((square_coefficient(p,wanted,variables) for p in rows),Poly.integer(0))
    require(exact==parse(coefficient),name+' nonzero leading coefficient')
    packet={'name':name,'domain':'unrestricted integers','variables':variables,'variable_count':len(variables),
        'fixed_ports':PORTS,'coefficient_binding':'../COEFFICIENT_BINDING.json',
        'residuals':[p.expression() for p in rows],'residual_count':len(rows),'residual_degrees':ds,
        'single_polynomial':'sum of squares of all listed residuals','exact_degree':expected_degree,
        'degree_certificate':{'monomial':wanted,'coefficient_expression':coefficient},
        'parent_restoration':restorations,'residual_expanded_terms':sum(len(p.terms) for p in rows),
        'proof':'../COORDINATE_PROOF.md'}
    if compact:
        packet['compact_specification']=compact
    (OUT/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
    return {k:packet[k] for k in ['name','variable_count','residual_count','residual_degrees','exact_degree','degree_certificate','residual_expanded_terms']}


def main():
    require((OUT/'octic25.json').is_file(),'run build_family.py first to reproduce the inherited baseline')
    verify_source_pins(); verify_coefficients()
    old=json.loads((OUT/'octic25.json').read_text())
    oldrows=[parse(x) for x in old['residuals']]
    incoming_pin=json.loads((ROOT/'INCOMING_PINS.json').read_text())['literal_baseline']
    incoming_data=(ROOT/incoming_pin['local_path']).read_bytes()
    require(hashlib.sha256(incoming_data).hexdigest()==incoming_pin['sha256'],'incoming baseline integrity')
    incoming=json.loads(incoming_data)
    incoming_rows=[parse(x) for x in incoming['residuals']]
    require(set(old['variables'])==set(incoming['variables']), 'incoming variable bridge')
    require(len(oldrows)==len(incoming_rows)==13,'incoming row count')
    bridge={2:parse('E-a'),3:parse('-E*(c-eta)'),5:parse('1')}
    order=[0,1,2,3,4,5,6,7,11,8,9,10,12]
    for i,(ours,source_index) in enumerate(zip(oldrows,order)):
        theirs=incoming_rows[source_index]
        require(ours==theirs+bridge.get(i,Poly.integer(0))*incoming_rows[11],
                'incoming unimodular row bridge '+str(i))
    definitions=[('J0','3*J3+1'),('W','4*(3*w3+1)'),('q','beta*J0+1'),('X','W*q'),
        ('Fbar','(K0+W)*C-z*(q-1)'),('Ebar','X*Y'),('abar','(X+1)*Y'),
        ('etabar','c-Y*k'),('zetabar','k-etabar'),('Vbar','f*o-c'),
        ('Delta','abar**2+4*abar+3'),('D','X+abar*c+gamma*(4*abar+3)'),
        ('R','(q-Fbar)*(q**3-q)-C*(q**2-1)+(MC+q*MF)*J0'),
        ('G','cone_A*Fbar*cone_B*C-(q-cone_A*Fbar-cone_B*C)**2'),
        ('Z','etabar*zetabar')]
    aliases={}
    for key,text in definitions:
        aliases[key]=parse(text,aliases)
    restoration={'F':'Fbar','alpha':'q-Fbar-C','a':'abar','E':'Ebar','eta':'etabar',
        'zeta':'zetabar','V':'Vbar','tau':'tau_gap+Ebar*Y*k'}
    substitutions={key:parse(value,aliases) for key,value in restoration.items()}
    deleted={1,2,6,7}
    rows=[]
    for i,p in enumerate(oldrows):
        new=p.substitute(substitutions)
        if i in deleted:
            require(new==0,'monic defining row '+str(i))
        else:
            rows.append(new)
    changes={'alpha':'C','a':'Y','zeta':'k','tau':'tau_gap'}
    variables=[changes.get(v,v) for v in old['variables'] if v not in ['F','E','eta','V']]
    require(len(variables)==21 and len(rows)==9,'21-variable dimension')
    display=['Y-(2*v_scale+1)*q**3',
        'tau_gap**2+(2*tau_gap-k)*Ebar*Y*k-1',
        'D**2-Delta*c**2-1',
        'k-1-h*Ebar-R',
        'Vbar-j*c+k-1-h*Ebar',
        'I-(2*r+1)*c**2',
        'I**2-Delta*(f**2-1)',
        'y**2-1-I**2*(y**2-Vbar**2)',
        'G*Z-(pair_root**2-G-Z+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)']
    for i,(actual,text) in enumerate(zip(rows,display)):
        require(actual==parse(text,aliases),'21-variable display transcription '+str(i))
    full_restoration={key:p.expression() for key,p in substitutions.items()}
    summary=[emit('coordinate21_degree16',variables,rows,16,{'Y':8,'k':8},'1',
        {'parent':'octic25.json','polynomial_map':full_restoration,'deleted_parent_rows_zero_based':sorted(deleted)},
        {'definitions':dict(definitions),'residuals':display})]
    # Integral auxiliary-root translation followed by a monic I projection.
    sub20={'I':parse('(2*r+1)*c**2'),'y':parse('f*o+y_gap')}
    rows20=[]
    for i,p in enumerate(rows):
        new=p.substitute(sub20)
        if i==5:
            require(new==0,'I defining row')
        else:
            rows20.append(new)
    variables20=[('y_gap' if v=='y' else v) for v in variables if v!='I']
    summary.append(emit('coordinate20_degree18',variables20,rows20,18,
        {'r':4,'c':10,'f':2,'o':2},'64',
        {'parent':'coordinate21_degree16.json','polynomial_map':{'I':'(2*r+1)*c**2','y':'f*o+y_gap'},
         'deleted_parent_rows_zero_based':[5]}))
    # The new family allows one more polynomial projection at lower degree
    # than the inspected 19-integer/degree-88 incoming point.
    q=aliases['q']
    sub19={'Y':parse('(2*v_scale+1)')*q**3}
    rows19=[]
    for i,p in enumerate(rows20):
        new=p.substitute(sub19)
        if i==0:
            require(new==0,'Y defining row')
        else:
            rows19.append(new)
    variables19=[v for v in variables20 if v!='Y']
    summary.append(emit('coordinate19_degree40',variables19,rows19,40,
        {'v_scale':8,'J3':24,'k':8},'2**8*3**24*beta**24',
        {'parent':'coordinate20_degree18.json','polynomial_map':{'Y':'(2*v_scale+1)*(beta*(3*J3+1)+1)**3'},
         'deleted_parent_rows_zero_based':[0]}))
    result={'status':'PASS','source':'independently reproduced zero-equivalent variant of the incoming octic25',
        'incoming_row_bridge':{'fixed_incoming_row_zero_based':11,'incoming_row_order':order,
            'changed_rows_zero_based':{str(i):p.expression() for i,p in bridge.items()},
            'description':'ours[i]=incoming[order[i]]+multiplier*incoming[11]; a reversible elementary row operation and permutation'},
        'new_results':summary,'scope':'exact local polynomial identities, dimensions, and degree certificates; semantic equivalence by the written polynomial-bijection proof'}
    (ROOT/'COORDINATE_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
