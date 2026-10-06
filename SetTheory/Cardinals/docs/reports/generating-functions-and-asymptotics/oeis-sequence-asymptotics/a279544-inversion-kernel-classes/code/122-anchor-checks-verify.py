#!/usr/bin/env python3
"""Run report122 exact checks; output must be outside the delivered package.
Usage: python -B checks/verify.py --output /absolute/external/results.json
All guards remain active with python -O. No network or non-stdlib import.
"""
import sys
sys.dont_write_bytecode=True
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
from exact_model import require, finite_checks, inversion_algebra_check
from exact_analytic import analytic_checks

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
FILES={'README.md','certificate.json','exact_model.py','exact_analytic.py','verify.py','negative_tests.py'}


def object_pairs(pairs):
    d={}
    for k,v in pairs:
        require(k not in d,'schema: duplicate JSON key '+k)
        d[k]=v
    return d


def load(path):
    try:
        return json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=object_pairs,
                          parse_constant=lambda x: (_ for _ in ()).throw(ValueError('schema: nonfinite JSON number')))
    except (OSError,UnicodeError,json.JSONDecodeError) as e:
        raise ValueError('schema: cannot read JSON '+path.name) from e


def keys(value,expected,label):
    require(type(value) is dict and set(value)==set(expected),'schema: '+label+' keys')


def integer(value,label,minimum=None,maximum=None):
    require(type(value) is int,'schema: '+label+' must be integer, not boolean')
    require(minimum is None or value>=minimum,'schema: '+label+' below minimum')
    require(maximum is None or value<=maximum,'schema: '+label+' above maximum')


def rational(value,label):
    require(type(value) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)/[1-9][0-9]*',value) is not None,'schema: '+label+' is not a canonical rational')
    r=Fraction(value)
    require(value==str(r.numerator)+'/'+str(r.denominator),'schema: '+label+' is not a canonical rational')
    return r


def inventory():
    inv=load(HERE/'inventory.json')
    keys(inv,{'schema','files'},'inventory'); integer(inv['schema'],'inventory schema',1,1)
    keys(inv['files'],FILES,'inventory file map')
    actual=set()
    for p in HERE.rglob('*'):
        require(not p.is_symlink(),'inventory: symlink is forbidden')
        require(p.is_file(),'inventory: unexpected directory '+str(p.relative_to(HERE)))
        actual.add(p.relative_to(HERE).as_posix())
    require(actual==FILES|{'inventory.json'},'inventory: closed file inventory mismatch')
    for name,sha in inv['files'].items():
        require(type(sha) is str and re.fullmatch('[0-9a-f]{64}',sha) is not None,'schema: invalid inventory digest')
        require(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==sha,'inventory: digest mismatch for '+name)
    return hashlib.sha256((HERE/'inventory.json').read_bytes()).hexdigest()


def schema(data):
    keys(data,{'schema','model','analytic','provenance'},'top-level'); integer(data['schema'],'version',1,1)
    m=data['model']; keys(m,{'direct_max_n','tree_max_n','identity_max_n','anchor_max_n','orbit_max_m','published_prefix','generated_terms','source_T_correction','orbit_next_differences'},'model')
    for k,n in [('direct_max_n',9),('tree_max_n',150),('identity_max_n',40),('anchor_max_n',64),('orbit_max_m',30)]:
        integer(m[k],k,n,n)
    require(type(m['published_prefix']) is list and len(m['published_prefix'])==26,'schema: published prefix length')
    for x in m['published_prefix']: integer(x,'published term',0)
    require(type(m['generated_terms']) is list and len(m['generated_terms'])==151,'schema: generated sequence length')
    for x in m['generated_terms']:
        require(type(x) is str and re.fullmatch(r'0|[1-9][0-9]*',x) is not None,'schema: generated term is not canonical integer string')
    rational(m['source_T_correction'],'source T correction')
    require(type(m['orbit_next_differences']) is list and len(m['orbit_next_differences'])==31,'schema: finite orbit list length')
    for x in m['orbit_next_differences']: rational(x,'orbit difference')
    a=data['analytic']; keys(a,{'iterations','lattice_digits','parameters','tail_E','derivative_tail','coefficient_tails','denominator_disk_B','denominator_modulus_floor','root_jet','claimed_intervals'},'analytic')
    integer(a['iterations'],'iterations',1,2048); integer(a['lattice_digits'],'lattice digits',120,120)
    keys(a['parameters'],{'rho','h','r','Z','M','q'},'parameters')
    for k,v in a['parameters'].items(): rational(v,k)
    for k in ('tail_E','derivative_tail','denominator_disk_B','denominator_modulus_floor'): rational(a[k],k)
    keys(a['coefficient_tails'],{'1','3','5'},'coefficient tails')
    for k,v in a['coefficient_tails'].items(): rational(v,'coefficient tail '+k)
    require(type(a['root_jet']) is list and len(a['root_jet'])==6,'schema: root jet length')
    for row in a['root_jet']:
        require(type(row) is list and len(row)==2,'schema: root jet row')
        for x in row: rational(x,'root jet coefficient')
    keys(a['claimed_intervals'],{'F','G_R','C','d1','d2'},'claimed intervals')
    for k,row in a['claimed_intervals'].items():
        require(type(row) is list and len(row)==2,'schema: interval pair')
        lo,hi=[rational(v,k+' endpoint') for v in row]
        require(lo<hi,'schema: reversed claimed interval '+k)
    p=data['provenance']; keys(p,{'source_urls','source_snapshot_sha256','implementation'},'provenance')
    require(p['source_urls']==['https://oeis.org/A279558','https://arxiv.org/html/2512.21943v3'],'schema: provenance source URLs')
    keys(p['source_snapshot_sha256'],{'certify.py','certify_corrections.py','global_bounds.py'},'provenance hashes')
    for v in p['source_snapshot_sha256'].values():
        require(type(v) is str and re.fullmatch('[0-9a-f]{64}',v) is not None,'schema: provenance hash')
    require(type(p['implementation']) is str and bool(p['implementation']),'schema: implementation provenance')
    return data


def run(stage):
    seal=inventory(); data=schema(load(HERE/'certificate.json'))
    result={'schema':1,'status':'PASS','stage':stage,'checks_inventory_sha256':seal,
            'certificate_sha256':hashlib.sha256((HERE/'certificate.json').read_bytes()).hexdigest()}
    if stage in ('all','preflight','analytic'): result['analytic']=analytic_checks(data['analytic'],stage=='preflight')
    if stage in ('all','finite'):
        result['finite']=finite_checks(data['model'])
        result['algebra']=inversion_algebra_check()
    require(inventory()==seal,'inventory: changed during verification')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--stage',choices=('all','preflight','analytic','finite','schema'),default='all')
    args=parser.parse_args(); out=args.output.resolve()
    require(not out.is_relative_to(PACKAGE),'output: path must be outside package')
    require(out!=HERE,'output: invalid destination')
    result=run(args.stage)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print('PASS report122 exact checks ('+args.stage+'); results: '+str(out))

if __name__=='__main__':
    try: main()
    except (ValueError,ZeroDivisionError) as error:
        print('FAIL '+str(error),file=sys.stderr); sys.exit(2)
