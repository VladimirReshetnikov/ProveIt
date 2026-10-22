#!/usr/bin/env python3
"""Audit owned finite recipes and constant folds against inert pinned JSON.

No received Python module is imported or executed. Numeric circuit fixtures
are algebra diagnostics, not admissible K215 coefficients or halting witnesses.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import importlib.util
import json
import random
import hashlib

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('owned_native_definition',ROOT/'k215_native_definition.py')
native=importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)


def check(value,message):
    if not value: raise ValueError(message)


def read(name):
    return json.loads((ROOT/name).read_text())


def fold(source):
    aliases={'scaled_t':'fixed_2d','odd_index':'fixed_2d_plus_b'}
    return [[name,op,aliases.get(a,a),aliases.get(b,b)]
            for name,op,a,b in source if name not in ('scaled_t','odd_index')]


def evaluate(source,values):
    env=dict(values)
    for name,op,a,b in source:
        a=env[a] if isinstance(a,str) else a
        b=env[b] if isinstance(b,str) else b
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def topology(source,free,outputs):
    known=set(free);definitions={}
    for name,op,a,b in source:
        check(name not in known,'Duplicate register')
        check(op in ('+','-','*'),'Unexpected operation')
        check(all(not isinstance(t,str) or t in known for t in (a,b)),'Forward dependency')
        known.add(name);definitions[name]=(a,b)
    live=set(outputs);todo=list(outputs)
    while todo:
        name=todo.pop()
        if name in definitions:
            for v in definitions[name]:
                if isinstance(v,str) and v not in live:
                    live.add(v);todo.append(v)
    check(set(definitions)<=live,'Dead computed register')
    check(set(free)<=live,'Dead free port')


def run():
    layout_receipt=read('complete75_half_binomial_compiler.json')
    fixture_inputs=[(0,[(0,)*9,(1,)*9],2),
                    (2,list(product(range(2),repeat=9))[:100],2),
                    (3,[(0,)*9,(1,)*9,(2,)*9],3),
                    (4,list(product(range(2),repeat=9))[:3],2)]
    layout_checks=[]
    for index,windows,a in fixture_inputs:
        got=native.compile_native_layout(windows,a)
        old=layout_receipt['layouts'][index]
        actual={'alphabet':got['window_count'],'original_tiles':got['tile_count'],
                'native_positions':len(got['positions']), 'dummy_positions':len(got['dummy']),
                'zero_clause_padding':got['zero_clause_padding'],
                'mask_population':sum(c.bit_count() for c in got['MF_old_poly'].values()),
                'inner_bits':got['b'],'cell_bits':got['d'],'inner_cell_length':got['L'],
                'anchors':list(got['anchors']),'high_correction':got['high_correction'],
                'high_degree':got['high_degree'],'extra_dummy':got['extra_dummy']}
        check(all(old[k]==v for k,v in actual.items()),'Native layout differs from pinned receipt')
        layout_checks.append({'receipt_index':index,**actual})
    check({r['high_correction'] for r in layout_checks}=={0,1},'Correction branch missing')
    parent84=read('complete84_scaled_strong_output.json')['packet']
    child82=read('k215_native82_source.json')
    parent74=next(f['packet'] for f in read('complete74_factored_first_norm.json')['forms']
                  if f['mode']=='signed20')
    child72=read('k215_native72_system.json')
    check(child82['source']==fold(parent84['source']),'82 source is not the exact constant fold')
    check(child72['source']==fold(parent74['source']),'72 source is not the exact constant fold')
    check(child72['sum_of_squares_source']==fold(parent74['polynomial_source']),
          '98 source is not the exact constant fold')
    check(child72['comparisons']==parent74['comparisons'],'Comparison changed')
    for source,free,outputs,M,A in [
        (child82['source'],child82['positive_witnesses']+child82['fixed_numerals'],['polynomial'],46,36),
        (child72['source'],child72['positive_witnesses']+child72['fixed_numerals'],
         [x for p in child72['comparisons'] for x in p],39,33),
        (child72['sum_of_squares_source'],child72['positive_witnesses']+child72['fixed_numerals'],
         [child72['sum_of_squares_output']],48,50)]:
        topology(source,free,outputs)
        counter=Counter(row[1] for row in source)
        check(counter['*']==M and counter['+']+counter['-']==A,'Gate ledger mismatch')
    rng=random.Random(82187220); numeric=0
    for parent,child,output,parent_source,child_source in [
        (parent84,child82,'polynomial',parent84['source'],child82['source']),
        (parent74,child72,parent74['output'],parent74['polynomial_source'],
         child72['sum_of_squares_source'])]:
        for n in range(128):
            values={name:rng.randrange(-5,6) for name in parent['witnesses']}
            values.update({name:rng.randrange(1,7) for name in parent['fixed_numerals']})
            values['x']=1
            got=dict(values,fixed_2d=values['twice_cell_bits'],
                     fixed_2d_plus_b=values['twice_cell_bits']+values['inner_bits'])
            check(evaluate(parent_source,values)[output]==evaluate(child_source,got)[output],
                  'Numeric constant-fold identity failed')
            numeric+=1
    return {'status':'PASS_NATIVE_SPECIALIZATION_AUDIT',
            'machine_checks':native.finite_checks(ROOT/'k215.tm'),
            'pinned_layout_fields_matched':layout_checks,
            'all_three_sources_exact_constant_folds':True,
            'all_source_gates_and_free_ports_live':True,
            'diagnostic_complete_polynomial_evaluations':numeric,
            'ledger82':{'M':46,'A':36,'positive_witnesses':18,'degree':187},
            'ledger72':{'M':39,'A':33,'positive_witnesses':20,'comparisons':9},
            'ledger98':{'M':48,'A':50,'positive_witnesses':20,'degree':84},
            'full_K215_window_enumeration':False,'full_K215_coefficients_materialized':False,
            'scope':'Exact circuit and finite recipe diagnostics. Mathematical proof supplies general simulation and compiler semantics.',
            'read_only_source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                                     for p in [ROOT/'complete84_scaled_strong_output.json',
                                               ROOT/'complete74_factored_first_norm.json',
                                               ROOT/'complete75_half_binomial_compiler.json']}}


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
