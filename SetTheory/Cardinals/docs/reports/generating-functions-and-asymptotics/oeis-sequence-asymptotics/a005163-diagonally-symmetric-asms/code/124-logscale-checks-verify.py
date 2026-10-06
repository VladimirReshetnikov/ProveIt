#!/usr/bin/env python3
"""Offline finite companion for report124. Outputs JSON; active under python -O."""
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
import algebra as a
ROOT=Path(__file__).resolve().parent
INVENTORY=['README.md','algebra.py','fixtures.json','inventory.json','negative_tests.py','verify.py']
RANGES={'dsasm_n_max':10,'determinant_t':['0','1','3/2','3','5'],
        'hahn_degree_max':12,'cubic_matrix_n_max':10,'contiguous_n_max':16,
        'projection_dimensions':[[5,2],[6,3],[8,4]]}
PROVENANCE={
    'DSASM':{'authors':'R. E. Behrend, I. Fischer, C. Koutschan','url':'https://arxiv.org/html/2309.08446v3','location':'Original skew Pfaffian and equation (4.11), at r=1'},
    'ASM_calibration':{'authors':'C. Krattenthaler','url':'https://www.mat.univie.ac.at/~kratt/akkomb/detsurv.pdf','location':'Theorem 34, equation (3.24), q=1 shifted Andrews determinant'},
    'classical_polynomials':{'authors':'H. Rosengren','url':'https://arxiv.org/pdf/1204.3424','location':'Section 3 Wilson and Meixner-Pollaczek input; specialized reductions are derived in report124'},
    'continuous_Hahn':'https://dlmf.nist.gov/18.22#E14',
    'Jacobi_normalization':'https://dlmf.nist.gov/18.3#T1',
    'Jacobi_contiguous':'https://dlmf.nist.gov/18.9#E6',
    'Fourier_beta_integral':'https://dlmf.nist.gov/5.12#E1',
    'gamma_ratio':'https://dlmf.nist.gov/5.11#iii',
    'implementation':'Fresh rational implementations for report124; inherited reference values are identified separately',
    'arithmetic':'Python standard library; exact integers and Fraction; no network or floating point'}
HISTORY={
    'source_report':'report121',
    'source_file':'checks/fixtures.json in the delivered report121 package',
    'source_file_bytes':3470,
    'source_file_sha256':'a9aa4c6a2eea07b5fdb7b6b3282d27da170f37ff634d516d9c8568015373b2ac',
    'source_date':'2026-10-02',
    'reuse':'Exact extraction of small_z for n=0..6 and ell_at_3 for n=1..10; inherited reference data, independently recomputed here',
    'historical_limit':'Report121 did not certify the DSASM logarithmic power or an O(1) remainder; this reuse makes no retroactive claim'}
LIMITATIONS=[
    'Finite exact identities and selected algebraic certificates supplement the report proofs; they do not certify any all-size analytic O(1) estimate.',
    'Jacobi endpoint bounds, weighted Hardy Hilbert-Schmidt estimates, trace-class comparisons, strong convergence, Hurwitz arguments and analytic Stirling remainders are not established by finite computation.',
    'Rational finite projections illustrate exact noncommuting identities; they are not numerical approximations to the DSASM Hardy operators.',
    'Fourier checks verify polynomial transforms, phases and algebraic normalization, with beta/gamma identities as stated analytic inputs; they are not an independent quadrature or proof of Fourier inversion.',
    'The inverse-center checks certify formal algebra only. They do not supply effective constants, a finite-threshold algorithm, an amplitude, residual convergence, parity matching or a real-valued o(1) integer inverse.',
    'Inherited report121 reference data retain their historical provenance. Fresh recomputation does not broaden the older report conclusions.',
    'The closed inventory detects accidental changes, not a coordinated rewrite of both verifier and manifest; the enclosing package must hash inventory.json.'
]

def keys(value,wanted,code): a.require(type(value) is dict and set(value)==set(wanted),code)
def same_typed(x,y):
    if type(x) is not type(y): return False
    if type(y) is dict: return set(x)==set(y) and all(same_typed(x[k],y[k]) for k in y)
    if type(y) is list: return len(x)==len(y) and all(same_typed(a,b) for a,b in zip(x,y))
    return x==y

def read_json(path,code):
    def pairs(items):
        out={}
        for k,v in items:
            a.require(k not in out,code+'_DUPLICATE_KEY',k); out[k]=v
        return out
    try:
        return json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=pairs,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    except a.Failure: raise
    except (OSError,UnicodeError,ValueError) as ex: raise a.Failure(code,str(ex)) from None

def rational(value,code):
    a.require(type(value) is str and len(value)<500 and re.fullmatch(r'-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?',value) is not None,code)
    q=F(value); a.require(str(q)==value,code+'_CANONICAL'); return q

def integrity():
    a.require(sorted(p.name for p in ROOT.iterdir())==INVENTORY,'INVENTORY_UNEXPECTED_OR_MISSING')
    for p in ROOT.iterdir(): a.require(p.is_file() and not p.is_symlink(),'INVENTORY_FILE_TYPE',p.name)
    m=read_json(ROOT/'inventory.json','INVENTORY_JSON'); keys(m,['schema_version','files'],'INVENTORY_SCHEMA')
    a.require(type(m['schema_version']) is int and m['schema_version']==1,'INVENTORY_VERSION')
    keys(m['files'],[name for name in INVENTORY if name!='inventory.json'],'INVENTORY_FILES_SCHEMA')
    for name,record in m['files'].items():
        keys(record,['bytes','sha256'],'INVENTORY_RECORD_SCHEMA')
        a.require(type(record['bytes']) is int and record['bytes']>0,'INVENTORY_SIZE_FORMAT')
        a.require(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}',record['sha256']) is not None,'INVENTORY_HASH_FORMAT')
        data=(ROOT/name).read_bytes()
        a.require(len(data)==record['bytes'],'INVENTORY_SIZE_MISMATCH',name)
        a.require(hashlib.sha256(data).hexdigest()==record['sha256'],'INVENTORY_HASH_MISMATCH',name)
    return len(INVENTORY)

def fixture():
    f=read_json(ROOT/'fixtures.json','FIXTURE_JSON')
    keys(f,['schema_version','report','ranges','provenance','historical','limitations'],'FIXTURE_SCHEMA')
    a.require(type(f['schema_version']) is int and f['schema_version']==1,'FIXTURE_VERSION')
    a.require(f['report']=='report124','FIXTURE_REPORT')
    a.require(same_typed(f['ranges'],RANGES),'FIXTURE_RANGES')
    a.require(same_typed(f['provenance'],PROVENANCE),'FIXTURE_PROVENANCE')
    a.require(same_typed(f['limitations'],LIMITATIONS),'FIXTURE_LIMITATIONS')
    keys(f['historical'],['provenance','small_z','ell_at_3'],'HISTORICAL_SCHEMA')
    h=f['historical']; a.require(same_typed(h['provenance'],HISTORY),'HISTORICAL_PROVENANCE')
    keys(h['small_z'],[str(n) for n in range(7)],'HISTORICAL_SMALL_Z_SCHEMA')
    for n,p in h['small_z'].items(): a.require(type(p) is list and len(p)==int(n)+1 and all(type(x) is int and 0<=x<10**8 for x in p),'HISTORICAL_SMALL_Z_VALUE')
    keys(h['ell_at_3'],[str(n) for n in range(1,11)],'HISTORICAL_DERIVATIVE_SCHEMA')
    for x in h['ell_at_3'].values(): rational(x,'HISTORICAL_DERIVATIVE_VALUE')
    return f

def run():
    count=integrity(); f=fixture()
    checks={
        'dsasm_and_calibration':a.dsasm_checks(RANGES,f['historical']),
        'continuous_Hahn_Jacobi_Fourier':a.hahn_jacobi_checks(RANGES),
        'scalar_contiguous_gamma':a.scalar_checks(RANGES),
        'finite_operator_identities':a.matrix_checks(RANGES),
        'inverse_center':a.inverse_center_checks()}
    return {'status':'PASS','report':'report124','schema_version':1,'closed_inventory_files':count,'ranges':RANGES,'checks':checks,'limitations':LIMITATIONS}

def main():
    try:
        a.require(len(sys.argv)==1,'UNEXPECTED_ARGUMENTS')
        print(json.dumps(run(),indent=2,sort_keys=True)); return 0
    except a.Failure as ex:
        print(json.dumps({'status':'FAIL','diagnostic':ex.code,'detail':ex.detail},sort_keys=True)); return 1
    except Exception as ex:
        print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':type(ex).__name__+': '+str(ex)},sort_keys=True)); return 2
if __name__=='__main__': sys.exit(main())
