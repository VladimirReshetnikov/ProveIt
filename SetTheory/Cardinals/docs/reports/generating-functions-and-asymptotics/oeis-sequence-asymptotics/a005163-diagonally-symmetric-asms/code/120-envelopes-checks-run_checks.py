#!/usr/bin/env python3
"""Offline exact report120 checks, with strict schemas and sealed file inventory."""
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
from support import CheckFailure, need, exact_json, keys, rational, integrity
import exact_math as m
import interval_math as im
ROOT=Path(__file__).resolve().parent
PROVENANCE={
 'sequence':'A005163','offset':1,'external_term_count':20,
 'oeis_url':'https://oeis.org/A005163',
 'paper_url':'https://arxiv.org/html/2309.08446v3',
 'paper_title':'Diagonally symmetric alternating sign matrices',
 'paper_authors':'Roger E. Behrend, Ilse Fischer, Christoph Koutschan',
 'paper_version_date':'2026-10-01',
 'paper_inputs':'Pfaffian count; equation (4.11); section 5.1; Proposition 5.1 equation (5.10)',
 'Andrews_source_url':'https://www.mat.univie.ac.at/~kratt/akkomb/detsurv.pdf',
 'Andrews_source_location':'Theorem 34, equation (3.24), q to 1, shifted index n+1',
 'prefix_provenance':'20 published OEIS terms transcribed in the source verification; independently recomputed here',
 'checked_date':'2026-10-02',
 'network_requirement':'None; the OEIS b-file is not used'
}
RANGES={'matrix_n_max':5,'graph_n_max':4,'kernel_grid_size':21,
 'determinant_polynomial_n_max':10,'transform_n_max':8,
 'triangular_n_max':10,'calibration_n_max':16}
DISPLAYS={
 'p':['0.2632463454286169293260401267680','0.2632463454286169293260401267681'],
 'q':['0.2960487268742950122628240495510507','0.2960487268742950122628240495510786'],
 'width':['0.1253798291941521304554959668203247','0.1253798291941521304554959668208131']
}
LIMITATIONS=[
 'Finite orientation and matrix enumeration are supplementary checks of the published bijection.',
 'Real-rootedness is proved by the analytic stability argument in the report, not by finite numerical root tests.',
 'An independent-Bernoulli representation of the total diagonal count does not assert independence of the actual diagonal entries.',
 'Finite determinant checks supplement the all-size identities and the classical shifted Andrews determinant theorem.',
 'The full DSASM asymptotic equivalent, limiting linear coefficient, actual logarithmic power and multiplicative amplitude remain open here.',
 'The bounded-remainder envelope constants and the onset of the two-ceiling inverse bracket are existential, not numerically effective.',
 'No common even-odd calibration amplitude, simple-root, interlacing or general r-weighted stability claim is used.',
 'Bibliographic novelty is not certified.'
]


def fixed(value,expected,diagnostic):
    keys(value,expected,diagnostic+'_SCHEMA')
    for key,want in expected.items():need(type(value[key]) is type(want) and value[key]==want,diagnostic+'_'+key.upper())


def fixture():
    f=exact_json(ROOT/'fixtures.json','FIXTURE_JSON')
    keys(f,['schema_version','provenance','ranges','external_prefix','small_z','stirling','enclosures','limitations'],'FIXTURE_SCHEMA')
    need(type(f['schema_version']) is int and f['schema_version']==1,'FIXTURE_VERSION')
    fixed(f['provenance'],PROVENANCE,'PROVENANCE');fixed(f['ranges'],RANGES,'RANGE')
    need(type(f['external_prefix']) is list and len(f['external_prefix'])==20,'PREFIX_LENGTH')
    need(all(type(v) is int and 0<v<10**26 for v in f['external_prefix']),'PREFIX_INTEGER')
    keys(f['small_z'],[str(n) for n in range(1,6)],'SMALL_Z_SCHEMA')
    for n,polynomial in f['small_z'].items():
        need(type(polynomial) is list and len(polynomial)==int(n)+1,'SMALL_Z_LENGTH')
        need(all(type(v) is int and 0<=v<10**5 for v in polynomial),'SMALL_Z_INTEGER')
    keys(f['stirling'],['contributions','ratio_inverse_N','even_logarithm'],'STIRLING_SCHEMA')
    need(type(f['stirling']['contributions']) is list and len(f['stirling']['contributions'])==4,'STIRLING_LENGTH')
    for v in f['stirling']['contributions']+[f['stirling']['ratio_inverse_N'],f['stirling']['even_logarithm']]:rational(v,'STIRLING_VALUE')
    keys(f['enclosures'],DISPLAYS,'ENCLOSURE_SCHEMA')
    for name,pair in f['enclosures'].items():
        need(type(pair) is list and len(pair)==2,'ENCLOSURE_LENGTH')
        for v in pair:need(type(v) is str and len(v)<100 and re.fullmatch(r'0\.[0-9]+',v),'ENCLOSURE_VALUE')
        need(pair==DISPLAYS[name],'ENCLOSURE_'+name.upper())
    need(f['limitations']==LIMITATIONS,'LIMITATIONS')
    return f


def run():
    count=integrity(ROOT);f=fixture()
    try:certificate=im.verify_intervals(f['enclosures'])
    except ValueError as error:raise CheckFailure('INTERVAL_CERTIFICATE',str(error)) from None
    return {'status':'PASS','report':'report120','sequence':'A005163','closed_inventory_files':count,
      'schema':'strict-v1','enumeration':m.enumeration_checks(f),'algebra':m.algebra_checks(f),
      'determinants':m.determinant_checks(f),'interval_certificate':certificate,'limitations':LIMITATIONS}


def main():
    try:print(json.dumps(run(),indent=2,sort_keys=True));return 0
    except CheckFailure as error:
        print(json.dumps({'status':'FAIL','diagnostic':error.name,'detail':error.detail},indent=2));return 1
    except Exception as error:
        print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':type(error).__name__+': '+str(error)},indent=2));return 2
if __name__=='__main__':sys.exit(main())
