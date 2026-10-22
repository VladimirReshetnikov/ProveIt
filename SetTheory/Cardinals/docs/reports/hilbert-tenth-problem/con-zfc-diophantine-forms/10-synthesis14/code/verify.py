#!/usr/bin/env python3
"""Rebuild and verify this package with the Python standard library.

Run from any working directory. By default this regenerates derived circuit
JSON and component receipts, then checks every circuit and the three literal
K215 transition tables. --full additionally repeats the finite 13-class
left/right census. No mode expands the enormous fixed coefficients, searches
for a K215 halt, compiles Lean/Rocq, or proves ZFC consistency.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
CODE=ROOT/'code'
VERIFICATION=ROOT/'verification'
PRIME=1_000_000_007

def require(condition,message):
    if not condition:raise ValueError(message)

def read_json(path):
    def pairs(items):
        d={}
        for k,v in items:
            require(k not in d,'Duplicate JSON key '+k)
            d[k]=v
        return d
    return json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=pairs)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def save(name,value):
    (VERIFICATION/name).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n',encoding='utf-8')

def run(relative,*args):
    command=[sys.executable,str(ROOT/relative),*map(str,args)]
    result=subprocess.run(command,cwd=ROOT,text=True,capture_output=True)
    if result.returncode:
        raise RuntimeError(relative+' failed:\n'+result.stdout[-4000:]+result.stderr[-4000:])
    return {'script':relative,'exit_code':result.returncode,'sha256':sha(ROOT/relative)}

def table_binding():
    helper=ROOT/'evidence/legacy-code/verify_k215.py'
    spec=importlib.util.spec_from_file_location('legacy_k215_table_parser',helper)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    files={name:ROOT/'machine'/name for name in ['k215.tm','KDense215.lean','Table215.v']}
    rows=module.parse_tm(files['k215.tm'].read_bytes())
    require(rows==module.parse_lean(files['KDense215.lean'].read_bytes()),'Lean table mismatch')
    require(rows==module.parse_rocq(files['Table215.v'].read_bytes()),'Rocq table mismatch')
    require(len(rows)==430,'Wrong transition count')
    require(rows[0]==(0,0,1,1,93),'Wrong first transition')
    terminals=[list(row) for row in rows if row[4]==215]
    require(terminals==[[68,1,1,1,215]],'Wrong halting transition')
    result={'status':'PASS','working_states':215,'transition_count':len(rows),
            'first_transition':list(rows[0]),'halting_transitions':terminals,
            'lean_literal_match':True,'rocq_literal_match':True,
            'source_sha256':{name:sha(path) for name,path in files.items()},
            'scope':'Finite literal table equality only; no Lean/Rocq build or unbounded halting verification.'}
    save('table_binding.json',result)
    return result

def output_comparisons(packet):
    if packet.get('comparisons'):return packet['comparisons']
    if packet.get('equations'):return packet['equations']
    names=packet.get('outputs') or [packet['output']]
    return [[name,0] for name in names]

def static_ledger(packet,comparisons):
    rows=packet['source'];free=packet['witnesses']+packet['fixed_numerals']
    require(len(set(free))==len(free),'Duplicate supplied port')
    known=set(free);producer={};counts=Counter()
    for row in rows:
        require(isinstance(row,list) and len(row)==4,'Malformed arithmetic row')
        name,op,a,b=row
        require(isinstance(name,str) and name not in known,'Duplicate register '+str(name))
        require(op in ['+','-','*'],'Unknown operation')
        require(all(type(v) is int or type(v) is str and v in known for v in (a,b)),
                'Unbound operand at '+name)
        producer[name]=row;known.add(name);counts[op]+=1
    need={v for pair in comparisons for v in pair if type(v) is str}
    require(need<=known,'Unbound circuit output')
    for name,op,a,b in reversed(rows):
        if name in need:need.update(v for v in (a,b) if type(v) is str)
    require(set(producer)<=need,'Dead arithmetic gate')
    require(set(free)<=need,'Dead supplied port')
    ledger={'operations':len(rows),'M':counts['*'],'A':counts['+']+counts['-'],
            'all_gates_live':True,'all_ports_live':True}
    for key in ['operations','M','A']:
        require(packet['ledger'][key]==ledger[key],'Ledger mismatch '+key)
    return ledger,producer

def formal_degrees(packet,producer):
    """Uniform polynomial upper bound; main-norm cancellation is bound first."""
    degree={x:1 for x in packet['witnesses']}
    degree.update({x:0 for x in packet['fixed_numerals']})
    identities=[]
    def d(x):return 0 if type(x) is int else degree[x]
    binding={
      'norm_main':['norm_main','-','L15','Ac2'],
      'L15':['L15','*','R14','R14'],
      'R14':['R14','+','D1','gam'],
      'D1':['D1','+','wn2','cam2'],
      'cam2':['cam2','*','R10a','R12'],
      'Ac2':['Ac2','*','A','c2'],
      'A':['A','+','a_square','a4m5'],
      'a_square':['a_square','*','R12','R12'],
      'c2':['c2','*','R10a','R10a']}
    for name,op,a,b in packet['source']:
        degree[name]=d(a)+d(b) if op=='*' else max(d(a),d(b))
        if name=='norm_main':
            require(all(producer.get(n)==row for n,row in binding.items()),'Unbound main-norm identity')
            u=max(d('wn2'),d('gam'))
            degree[name]=max(d('cam2')+u,2*u,d('a4m5')+2*d('R10a'))
            identities.append({'register':name,
               'identity':'(ac+X+gamma H)^2-(a^2+H)c^2=2ac(X+gamma H)+(X+gamma H)^2-Hc^2',
               'upper_degree':degree[name]})
    return degree,identities

def poly_add(a,b,sign=1):
    z=[0]*max(len(a),len(b))
    for i in range(len(z)):
        z[i]=((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%PRIME
    while len(z)>1 and not z[-1]:z.pop()
    return z

def poly_mul(a,b):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%PRIME
    while len(z)>1 and not z[-1]:z.pop()
    return z

def diagnostic_line(packet,seed):
    rng=random.Random(seed)
    values={n:[rng.randrange(1,8),rng.randrange(1,12)] for n in packet['witnesses']}
    require(len(packet['fixed_numerals'])==4,'Unexpected diagnostic coefficient interface')
    values.update({n:[v] for n,v in zip(packet['fixed_numerals'],(31,127,10,45))})
    def p(x):return [x%PRIME] if type(x) is int else values[x]
    for name,op,a,b in packet['source']:
        values[name]=poly_mul(p(a),p(b)) if op=='*' else poly_add(p(a),p(b),1 if op=='+' else -1)
    return values

def source_audit(packet,path,seed):
    comparisons=output_comparisons(packet)
    ledger,producer=static_ledger(packet,comparisons)
    degrees,identities=formal_degrees(packet,producer)
    lines=diagnostic_line(packet,seed)
    def d(x):return 0 if type(x) is int else degrees[x]
    def v(x):return [x%PRIME] if type(x) is int else lines[x]
    upper=[max(d(a),d(b)) for a,b in comparisons]
    residuals=[poly_add(v(a),v(b),-1) for a,b in comparisons]
    observed=[len(p)-1 if any(p) else -1 for p in residuals]
    require(all(g<=u for g,u in zip(observed,upper)),'Diagnostic exceeds uniform upper bound')
    is_system=bool(packet.get('comparisons') or packet.get('equations'))
    if is_system:
        declared=packet.get('residual_exact_degrees')
        if declared is None and packet.get('degree_upper'):
            declared=[packet['degree_upper'][a] for a,b in comparisons]
        if declared is not None:
            require(declared==upper,'System degree metadata mismatch '+str(path))
            require(observed==declared,'System degree attainment diagnostic failed '+str(path))
    else:
        declared=packet.get('exact_degree',packet.get('degree'))
        if declared is None:declared=packet.get('degree_upper',{}).get(comparisons[0][0])
        require(declared==upper[0],'Polynomial degree metadata mismatch '+str(path))
        require(observed[0]==declared,'Polynomial degree attainment diagnostic failed '+str(path))
    return {'file':path,'name':packet['name'],'status':'PASS',
            'variables':len(packet['witnesses']),'equations':len(comparisons),
            'domain':packet.get('witness_domain'),'ledger':ledger,
            'uniform_degree_upper_bounds':upper,'bound_identities':identities,
            'diagnostic_line':{'modulus':PRIME,'seed':seed,'degrees':observed,
                               'leading_coefficients':[p[-1] for p in residuals]},
            'degree_scope':'Upper bounds follow the bound source identities. Finite-field lines use small diagnostic coefficients; uniform nonzero leaders on the actual coefficient slice are proved in report.tex.'}

def quartic_audit(packet,path):
    variables=packet['variables'];fixed=packet['fixed_ports'];names=variables+fixed
    require(len(variables)==33 and len(set(names))==len(names),'Quartic variable interface')
    def sparse(terms):
        out={}
        for term in terms:
            require(type(term['coefficient']) is int,'Noninteger coefficient')
            require(set(term['powers'])<=set(names),'Unknown monomial variable')
            exponents=tuple(term['powers'].get(n,0) for n in names)
            require(all(type(v) is int and v>=0 for v in exponents),'Bad monomial exponent')
            require(exponents not in out,'Duplicate sparse monomial')
            out[exponents]=term['coefficient']
        return {m:c for m,c in out.items() if c}
    rs=[sparse(terms) for terms in packet['expanded_residuals']]
    require(len(rs)==24,'Wrong quadratic residual count')
    used={names[j] for p in rs for m in p for j,e in enumerate(m) if e}
    require(used==set(names),'Unused quartic variable or coefficient port')
    def degree(p):return max((sum(m[:len(variables)]) for m in p),default=-1)
    require(all(degree(p)<=2 for p in rs),'Residual exceeds degree two')
    sos={}
    for p in rs:
        for a,ca in p.items():
            for b,cb in p.items():
                m=tuple(x+y for x,y in zip(a,b));sos[m]=sos.get(m,0)+ca*cb
    sos={m:c for m,c in sos.items() if c}
    require(sos==sparse(packet['expanded_quartic']),'Expanded sum of squares mismatch')
    t=[0]*len(names);t[variables.index('tau')]=4
    require(sos.get(tuple(t))==1,'Missing uniform tau^4 coefficient')
    require(degree(sos)==packet['degree']==4,'Wrong quartic degree')
    require(len(sos)==packet['quartic_term_count'],'Wrong sparse term count')
    return {'file':path,'name':packet['name'],'status':'PASS','variables':33,
            'domain':packet['domain'],'quadratic_equations':24,'single_equation_degree':4,
            'expanded_terms':len(sos),'tau_fourth_power_coefficient':1,
            'ledger':None,'scope':'Exact sparse polynomial sum-of-squares identity and uniform degree certificate; no operation count is claimed for this presentation.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true',help='Also rerun the finite13-class left/right census')
    args=ap.parse_args()
    VERIFICATION.mkdir(parents=True,exist_ok=True)
    components=[]
    components.append(run('code/build_ordinary.py'))
    components.append(run('code/build_root14.py'))
    components.append(run('code/verify_signed_and_root.py'))
    count='coefficients/cross_count_verified.json'
    if args.full:
        count='verification/cross_count_full.json'
        components.append(run('evidence/legacy-code/count_blank_alphabet.py',
                              '--tm',ROOT/'machine/k215.tm','--output',ROOT/count))
    components.append(run('code/projected_cross_compiler.py',
                          '--inherited-count',count,'--legacy-code','evidence/legacy-code',
                          '--tm','machine/k215.tm','--output','verification/projected_cross.json'))
    tables=table_binding()
    audits=[]
    raw=read_json(ROOT/'evidence/base67.json');base=raw.get('packet',raw)
    audits.append(source_audit(base,'evidence/base67.json',2100))
    expected={'ordinary_blank_system_61.json','ordinary_blank_four_system_63.json',
              'ordinary_blank_sos_78.json','ordinary_blank_four_sos_74.json',
              'ordinary_blank_product69.json','ordinary_quartic33.json',
              'root14_product75.json','root14_outer73.json','root14_system69.json',
              'fixed_blank_67_integer33.json','fixed_blank_68_integer33.json'}
    require(expected<={p.name for p in (ROOT/'circuits').glob('*.json')},'Missing expected circuit artifact')
    for index,path in enumerate(sorted((ROOT/'circuits').glob('*.json')),2101):
        packet=read_json(path);relative=path.relative_to(ROOT).as_posix()
        audits.append(source_audit(packet,relative,index) if 'source' in packet else quartic_audit(packet,relative))
    save('circuit_audit.json',{'status':'PASS','circuits':audits})
    projected=read_json(VERIFICATION/'projected_cross.json')
    require(projected['verification']['status']=='PASS','Coefficient component did not pass')
    signed=read_json(VERIFICATION/'signed_root.json')
    require(signed['status']=='PASS','Signed/root component did not pass')
    ordinary=read_json(VERIFICATION/'ordinary.json')
    summary={'status':'PASS','schema':'proveit-con-zfc-synthesis-verification-v1',
             'source_commit':'3b201cdea32d2c816f5f3d20734051f25fd3ef14',
             'standard_library_only':True,'full_census_repeated':args.full,
             'components':components,'literal_table_binding':tables,
             'circuit_count_including_base':len(audits),
             'circuit_results':audits,
             'ordinary_identity_cases':ordinary['diagnostic_identity_cases'],
             'signed_root_identity_checks':signed,
             'projected_crosses':projected['constants']['projected_cross_count'],
             'coefficient_geometry':projected['constants']['layout'],
             'coefficient_receipt':'verification/projected_cross.json',
             'scope':'Reproducible finite arithmetic and source checks supplement the mathematical proofs. They do not establish the compiler theorem by sampling.',
             'not_performed':['expansion of astronomical fixed integers','enumeration of the full projected tile alphabet',
                              'an accepting K215 computation','a full accepting Pell witness','Lean/Rocq kernel builds','a proof of Con(ZFC)']}
    save('summary.json',summary)
    print(json.dumps({'status':'PASS','circuits_checked':len(audits),
                      'literal_transitions_checked':tables['transition_count'],
                      'projected_crosses':summary['projected_crosses'],
                      'cell_bits_power_five':summary['coefficient_geometry']['cell_bits_power_five'],
                      'summary':'verification/summary.json'},indent=2))

if __name__=='__main__':main()
