#!/usr/bin/env python3
"""Exact report119 arithmetic, strict fixture schema, and closed checks inventory.
Python >=3.10, standard library only. No asserts or floating-point proof inputs.
Use mutation_tests.py for bounded normal/-O and fresh-directory negative replay.
"""
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from support import CheckFailure, need, exact_json, keys, rational, interval, integrity
import exact_math as m
import jet_certificate as jets
ROOT=Path(__file__).resolve().parent
PROVENANCE={
 'sequence':'A279569','class':'1953A','offset':0,
 'oeis_url':'https://oeis.org/A279569',
 'paper_url':'https://arxiv.org/html/2512.21943v3',
 'paper_sections':'3.7 equations (3.38)-(3.39); 4.2 equation (4.11)',
 'retrieved_date':'2026-10-02',
 'external_scope':'26 displayed OEIS terms, n=0..25',
 'generated_scope':'n=26..60 are internal tree/orbit agreement, not external data',
 'source_asymptotic_status':'The paper labels Section 4.2 asymptotics non-rigorous'
}
RANGES={'tree_n_max':60,'orbit_n_max':60,'external_prefix_n_max':25,'brute_n_max':8,
 'functional_equation_n_max':16,'core_N':256,'arithmetic_places':100,
 'core_display_places':55,'atan5_terms':100,'atan239_terms':30,'gamma_order':6}
TAILS={'rho':'4/27','seed_radius':'1/1000','M':'181/100','q':'7/25',
 'value_error_power_of_two':244,'derivative_multiplier':1000,
 'product_power_of_two':230,'Q_bound_multiplier':14,'R_bound_multiplier':80}
JET_PARAMETERS={'N':400,'degree':5,'t_radius':'1/100000','R':'149/1000',
 'M':'181/100','q':'7/25','value_error_power_of_two':342,'Cauchy_multiplier':16,
 'product_power_of_two':327,'Q_bound_multiplier':14,'R_bound_multiplier':114,
 'printed_places':80,'rectangle_places':12}
LIMITATIONS=[
 'Finite coefficient agreement does not prove the generating-tree interpretation or convergence.',
 'The report proves the formal germ, normal holomorphy, real determinant gap, Pringsheim argument, boundary removability, and transfer hypotheses.',
 'Exact rational enclosures rely on the uniform complex tail and Cauchy inequalities proved in the report.',
 'All-order expansions are fixed-order asymptotic statements, without numerical remainder constants or threshold cutoffs.',
 'The count-index inverse requires its rounding bracket; a bare ceiling of an approximation is not certified.',
 'No novelty, nonalgebraicity, non-D-finiteness, or complete exponentially improved transseries claim is made.'
]
ENCLOSURES=['Q_plus','R_plus','Q_minus','R_minus','Q_plus_derivative','R_plus_derivative',
 'A_rho','F_v','pi','sqrt_3_over_pi','C']

def fixed_object(value,expected,code):
    keys(value,expected,code+'_SCHEMA')
    for key,want in expected.items():
        need(type(value[key]) is type(want) and value[key]==want,code+'_'+key.upper())

def fixture():
    f=exact_json(ROOT/'fixtures.json','FIXTURE_JSON')
    keys(f,['schema_version','provenance','ranges','tails','sequences','enclosures','gamma','corrections','limitations'],'FIXTURE_SCHEMA')
    need(type(f['schema_version']) is int and f['schema_version']==1,'FIXTURE_VERSION')
    fixed_object(f['provenance'],PROVENANCE,'PROVENANCE')
    fixed_object(f['ranges'],RANGES,'RANGE')
    fixed_object(f['tails'],TAILS,'TAIL')
    keys(f['sequences'],['external_prefix','internal_terms'],'SEQUENCE_SCHEMA')
    for key,n in [('external_prefix',26),('internal_terms',61)]:
        values=f['sequences'][key]
        need(type(values) is list and len(values)==n,'SEQUENCE_LENGTH')
        need(all(type(v) is int and 0<v<10**60 for v in values),'SEQUENCE_INTEGER')
    keys(f['enclosures'],ENCLOSURES,'ENCLOSURE_SCHEMA')
    for value in f['enclosures'].values():interval(value,55,'ENCLOSURE_VALUE')
    keys(f['gamma'],['transfer_coefficients','gamma_ratios'],'GAMMA_SCHEMA')
    keys(f['gamma']['transfer_coefficients'],['1/2','3/2','5/2','7/2'],'GAMMA_TRANSFER_SCHEMA')
    for name,values in list(f['gamma']['transfer_coefficients'].items())+[('ratios',f['gamma']['gamma_ratios'])]:
        need(type(values) is list and len(values)==(4 if name=='ratios' else 7),'GAMMA_LENGTH')
        for value in values:rational(value,'GAMMA_VALUE')
    c=f['corrections']
    keys(c,['parameters','root_jets','rectangle','enclosures'],'JET_SCHEMA')
    fixed_object(c['parameters'],JET_PARAMETERS,'JET_PARAMETER')
    keys(c['root_jets'],['plus','minus'],'JET_ROOT_SCHEMA')
    for root in c['root_jets'].values():
        need(type(root) is list and len(root)==6,'JET_ROOT_LENGTH')
        for pair in root:
            need(type(pair) is list and len(pair)==2,'JET_ROOT_PAIR')
            for v in pair:rational(v,'JET_ROOT_VALUE')
    keys(c['rectangle'],['D_real','D_imag','N_norm1_upper'],'JET_RECTANGLE_SCHEMA')
    for key in ['D_real','D_imag']:interval(c['rectangle'][key],12,'JET_RECTANGLE_VALUE')
    rational(c['rectangle']['N_norm1_upper'],'JET_RECTANGLE_VALUE')
    keys(c['enclosures'],['b1','b3','b5','C','c1','c2'],'JET_ENCLOSURE_SCHEMA')
    for v in c['enclosures'].values():interval(v,80,'JET_ENCLOSURE_VALUE')
    need(f['limitations']==LIMITATIONS,'LIMITATIONS')
    return f

def run():
    count=integrity(ROOT);f=fixture()
    result={'status':'PASS','report':'report119','sequence':'A279569',
            'closed_inventory_files':count,'schema':'strict-v1','algebra':m.algebra(),
            'gamma':m.gamma_checks(f),'leading':m.leading(f),'corrections':jets.check(f),
            'enumeration':m.enumeration(f),'limitations':LIMITATIONS}
    return result

def main():
    try:print(json.dumps(run(),indent=2,sort_keys=True));return 0
    except CheckFailure as e:
        print(json.dumps({'status':'FAIL','diagnostic':e.name,'detail':e.detail},indent=2));return 1
    except Exception as e:
        print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':type(e).__name__+': '+str(e)},indent=2));return 2
if __name__=='__main__':sys.exit(main())
