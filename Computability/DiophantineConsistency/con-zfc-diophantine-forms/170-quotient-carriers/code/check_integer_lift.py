#!/usr/bin/env python3
"""Independently check the exact positive-to-integer lift; no zero search."""
from pathlib import Path
from collections import Counter
import hashlib, importlib.util, json, sys

ROOT=Path(__file__).resolve().parents[1]
PARENT_SHA256='28bfcd4ae5fcacc363f6543ea088c09410d0d094b6156661ce547c87f18c8639'

def need(condition,message):
    if not condition:raise ValueError(message)

def load_parent_checker():
    path=ROOT/'compact/verify_fixed_carriers.py'
    spec=importlib.util.spec_from_file_location('_independent_positive_source_checker',path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def integer_topology(packet):
    inputs=packet['witnesses']+packet['fixed_numerals']
    seen=set(inputs);rows={}
    need(len(seen)==len(inputs),'Repeated input')
    for row in packet['source']:
        need(isinstance(row,list) and len(row)==4,'Malformed lift row')
        name,op,left,right=row
        need(isinstance(name,str) and name not in seen,'Repeated register')
        need(op in {'+','-','*'},'Nonpolynomial lift operation')
        need(all(type(v) is int or (isinstance(v,str) and v in seen)
                 for v in (left,right)),'Forward reference')
        seen.add(name);rows[name]=row
    live=set();todo=[packet['output']]
    while todo:
        name=todo.pop()
        if type(name) is int or name in live:continue
        need(name in seen,'Unknown output/reference')
        live.add(name)
        if name in rows:todo.extend(rows[name][2:])
    need(live==seen,'Dead lift input or register')
    counts=dict(Counter(row[1] for row in packet['source']))
    need(len(rows)==158==packet['operations'],'Wrong lift operation count')
    need(counts==packet['operation_counts']=={'*':78,'+':68,'-':12},'Wrong lift operation breakdown')

def check():
    path=ROOT/'equations/P36_integer.json';packet=json.loads(path.read_text())
    parent_path=ROOT/'compact/fixed_12_rational_74_degree438.json'
    parent=json.loads(parent_path.read_text())
    digest=hashlib.sha256(parent_path.read_bytes()).hexdigest()
    need(digest==PARENT_SHA256==packet['parent_sha256'],'Parent byte binding differs')
    need(packet['parent']=='../compact/fixed_12_rational_74_degree438.json','Unexpected parent path')
    need(parent['domain']=='strictly positive integers','Changed parent domain')
    need(packet['domain']=='unrestricted integers','Changed integer domain')
    checker=load_parent_checker()
    binding,_,_=checker.coefficient_check()
    checker.topology(parent,12,74,(42,20,12))
    checker.exact_cuts(parent,'rational')
    leader=checker.degrees_and_leader(parent,'rational',438)
    checker.parent_bindings(parent,binding)

    # Specify the entire prefix independently, then verify its full
    # polynomial action rather than trusting substitution metadata.
    expected_inputs=[];expected_prefix=[]
    for name in parent['witnesses']:
        aa,bb,cc=[name+'_'+k for k in ('a','b','c')]
        expected_inputs.extend([aa,bb,cc])
        expected_prefix += [
            [name+'__a2','*',aa,aa],[name+'__b2','*',bb,bb],
            [name+'__c1','+',cc,1],[name+'__cc1','*',cc,name+'__c1'],
            [name+'__ab','+',name+'__a2',name+'__b2'],
            [name+'__abc','+',name+'__ab',name+'__cc1'],
            [name,'+',name+'__abc',1],
        ]
    need(len(expected_inputs)==36,'Incorrect parent variable count')
    need(packet['witnesses']==expected_inputs,'Changed input order')
    need(packet['fixed_numerals']==parent['fixed_numerals'],'Changed fixed ports')
    need(packet['coefficient_binding']['ports']==parent['coefficient_binding']['ports'],'Changed coefficient tuple')
    need(packet['source'][:84]==expected_prefix,'Exact substitution prefix differs')
    need(packet['source'][84:]==parent['source'],'Appended parent DAG differs')
    need(packet['output']==parent['output'],'Changed output register')

    Poly=checker.Poly
    env={x:Poly.var(x) for x in expected_inputs}
    for name,op,left,right in packet['source'][:84]:
        a=Poly(left) if type(left) is int else env[left]
        b=Poly(right) if type(right) is int else env[right]
        env[name]=checker.operation(op,a,b)
    for name in parent['witnesses']:
        a,b,c=[Poly.var(name+'_'+k) for k in ('a','b','c')]
        need(env[name]==1+a*a+b*b+c*(c+1),'Substitution polynomial differs at '+name)
    integer_topology(packet)
    need(packet['exact_degree']==876,'Incorrect lift degree')
    expected_monomial={name+'_a':2*power for name,power in leader['monomial'].items()}
    need(packet['proof']['monomial']==expected_monomial,'Lift leading monomial differs')
    need(sum(expected_monomial.values())==876,'Leading monomial degree mismatch')
    need(leader['nonzero_coefficient_multiplier']==24 and leader['beta_exponent']==272,
         'Unexpected parent leading coefficient')
    need(packet['proof']['nonzero_coefficient']=='+24*beta^272','Changed coefficient statement')
    # Uniform upper bound: parent degree438 times substitution degree2.
    # Uniform attainment: in the homogeneous substitution select only
    # a_j^2 in every block. Distinct parent monomials have distinct
    # resulting exponent vectors, so the checked coefficient survives.
    return {
        'status':'pass','file':'equations/P36_integer.json',
        'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'parent_sha256':digest,'variables':36,'prefix_gates':84,
        'parent_gates':74,'operations':158,
        'operation_counts':dict(Counter(r[1] for r in packet['source'])),
        'exact_degree':876,'attained_monomial':expected_monomial,
        'attained_coefficient':'+24*beta^272',
        'all_inputs_and_gates_live':True,
        'scope':'Exact prefix, parent DAG and coefficient binding, domains, full polynomial substitutions, topology, liveness, counts and uniform degree certificate. No candidate zero was tested.'}

if __name__=='__main__':
    print(json.dumps(check(),indent=2))
