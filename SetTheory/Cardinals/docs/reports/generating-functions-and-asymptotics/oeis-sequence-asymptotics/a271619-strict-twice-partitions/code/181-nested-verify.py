#!/usr/bin/env python3
"""Exact finite verification for Report181, active also with Python -O."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent.parent
sys.path.insert(0,str(ROOT))
sys.path.insert(0,str(ROOT/'code'))
import exact
import verify_manifest as files

KNOWN=[1,1,2,4,8,15,28,51,92,164,289,504,871,1493,2539,4290,7201,12017,19939]
H_EXPECTED=['1','2','7','68/3','391/4','40043/90','96787/40','17366357/1260','157752233/1728','285439229213/453600']
# Pins are literal release-review anchors, independent of the package manifest.
PINS={'data/PROVENANCE.json': '58d46254bfb60aac5fa8fbcc02bb45ea9538ea6c5cff9d5b8ca6377003ee0aaa', 'data/references/FROZEN.json': 'cbc15e034a290c5a44668fc1e9188f9670d4079b921314333255beb8b20a8aee', 'data/references/exact_terms_0_600.txt': '2149f443f6524faec57311834867a404eae8a612b8fef70f5df6b59faa35c0ad', 'data/references/independent_checks.json': 'ca08fb612b28286b173a62ed4dfd7041133394fbe0fbacd30cfda88602e31b9a', 'data/references/marked_formal_coefficients.json': 'a3cf75cf5167eb66954f36881e13cb47765ab67a53952c0aa546c0b4c4d930bc', 'data/references/marked_verification.json': 'fa62631083f1098c847268429ccd5ab42d0faf6e305f2c3fb76d6498951cbb25', 'data/references/maximum_verification.json': '0b3bf83b9b51cedb55aad853f4cceb92e06df3ae8370c52da44c168748c1218b', 'data/references/verification.json': '50bfcac675413176cbc455790e0fb96c2741163328b99b6cff1ae47e613a970b', 'optional/scout/verify_marked.py': '0cf3a444091a2886b29c8e965610c5f03bb30cb2220e11d706d191fb9519d37b', 'optional/scout/verify_maximum.py': 'd5f4dea103e5bc90651376df72d9a12eb0f43a5cf34e4b040ae8f545d4fe37c6', 'optional/scout/verify_nested_partitions.py': '1bf6bc6dcffd664d8b27a18d5bea875bd3ce362068f772600f4145c5ad27d521'}


def need(condition,message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value,sort_keys=True,indent=2,ensure_ascii=True,allow_nan=False)+'\n').encode('utf-8')


def load_certificate(path):
    path=Path(path).absolute()
    files.check_directory(path.parent)
    value=files.load_json(files.read_regular(path).decode('utf-8'))
    need(isinstance(value,dict),'certificate must be an object')
    return value


def same(a,b):
    need(canonical(a)==canonical(b),'certificate differs from exact independent derivation')


def references():
    for name,digest in PINS.items():
        path=ROOT/files.safe_name(name)
        files.check_directory(path.parent)
        need(hashlib.sha256(files.read_regular(path)).hexdigest()==digest,
             'modified pinned reference: '+name)
    return dict(PINS)


def frozen_terms(path):
    path=Path(path).absolute()
    files.check_directory(path.parent)
    text=files.read_regular(path).decode('ascii')
    lines=text.splitlines()
    need(len(lines)==601,'frozen term count must be 601')
    values=[]
    for n,line in enumerate(lines):
        need(re.fullmatch(r'(?:0|[1-9][0-9]*) (?:0|[1-9][0-9]*)',line) is not None,
             'invalid frozen coefficient line')
        index,value=map(int,line.split(' '))
        need(index==n,'frozen coefficient index mismatch')
        values.append(value)
    need(text=='\n'.join(f'{n} {value}' for n,value in enumerate(values))+'\n',
         'noncanonical frozen coefficient file')
    return values


def manuscript_prefix(path):
    path=Path(path).absolute()
    files.check_directory(path.parent)
    text=files.read_regular(path).decode('utf-8')
    begin,end='% BEGIN VERIFIED OEIS PREFIX','% END VERIFIED OEIS PREFIX'
    need(text.count(begin)==text.count(end)==1,'manuscript prefix markers missing or duplicated')
    need(text.index(begin)<text.index(end),'manuscript prefix markers reversed')
    body=text.split(begin)[1].split(end)[0]
    match=re.fullmatch(r'\s*\\\[\s*([0-9,\s]+)\s*\\\]\s*',body)
    need(match is not None,'manuscript prefix must be a literal displayed integer list')
    chunks=match.group(1).split(',')
    need(all(re.fullmatch(r'\s*(?:0|[1-9][0-9]*)\s*',chunk) for chunk in chunks),
         'manuscript prefix contains a nonliteral or noncanonical term')
    need([int(chunk) for chunk in chunks]==KNOWN,'manuscript prefix does not match exact values')
    return len(KNOWN)


def derive():
    pins=references()
    coeffs=exact.product_coefficients(600)
    need(coeffs==frozen_terms(ROOT/'data/references/exact_terms_0_600.txt'),
         'ordinary convolution disagrees with frozen data')
    counts=[exact.composition_count(n) for n in range(19)]
    need(counts==coeffs[:19]==KNOWN,'independent composition counts disagree')
    need(all(coeffs[n]<coeffs[n+1] for n in range(1,600)),'finite monotonicity check failed')
    need(all(coeffs[n]<=2**(n-1) for n in range(1,601)),'finite composition bound failed')
    hs=[str(x) for x in exact.formal_h(10)[1:]]
    need(hs==H_EXPECTED,'formal h coefficients disagree')
    e1=exact.edgeworth_terms(1); e2=exact.edgeworth_terms(2)
    e1_expected={(0,1):('1/8',-2),(2,0):('-5/24',-3)}
    e2_expected={(0,0,0,1):('-1/48',-3),(0,2,0,0):('35/384',-4),
                 (1,0,1,0):('7/48',-4),(2,1,0,0):('-35/64',-5),
                 (4,0,0,0):('385/1152',-6)}
    for rows,expected in ((e1,e1_expected),(e2,e2_expected)):
        need({tuple(r['cumulant_powers']):(r['coefficient'],r['b_power']) for r in rows}==expected,
             'Edgeworth tuple coefficients disagree')
    lead1=exact.edgeworth_leading(1)
    need(lead1=={(3,-2):exact.Q(-35,144)},'E1 leading substitution disagrees')
    free=exact.free_energy_polynomial(10)
    early={k:v for k,v in free.items() if k[0]<=3}
    expected={(-3,2,0,0):exact.Q(1,2),(-2,1,1,0):exact.Q(1,2),
              (-2,0,0,1):exact.Q(-1),(-1,0,2,0):exact.Q(1,8),
              (-1,1,0,0):exact.Q(35,24),(0,0,1,0):exact.Q(11,48),
              (1,0,0,0):exact.Q(1225,1152),(2,0,0,0):exact.Q(5761,2880),
              (3,0,0,0):exact.Q(7)}
    need(early==expected,'displayed free-energy algebra disagrees')
    return {
        'schema_version':1,'report':181,'sequence':'A358836',
        'scope':{'ordinary_convolution_maximum_n':600,'direct_composition_maximum_n':18,
                 'formal_H_maximum_degree':10,'Edgeworth_orders_checked':[1,2],
                 'free_energy_positive_degree_checked':10,
                 'asymptotic_remainders_certified_by_code':False,
                 'floating_point_used_in_core':False,
                 'probability_limit_theorems_certified_by_code':False},
        'reference_sha256':pins,'coefficients_0_through_600':coeffs,
        'composition_counts_0_through_18':counts,
        'finite_strict_increase_a1_through_a600':True,
        'finite_composition_upper_bound_n_1_through_600':True,
        'h_1_through_h_10':hs,
        'E1':e1,'E2':e2,'Edgeworth_cumulant_basis':{'E1':[3,4],'E2':[3,4,5,6]},
        'E1_leading':{'basis':['t','A'],'terms':exact.poly_rows(lead1)},
        'E2_leading':{'basis':['t','A'],'terms':exact.poly_rows(exact.edgeworth_leading(2))},
        'free_energy':{'basis':['t','A','ell','Z'],'terms':exact.poly_rows(free),
                       'separate_terms':['-log(t)/12',"-zeta_prime(-1)"],
                       'substitutions':{'A':'pi^2/6','ell':'log(t/(2*pi))','Z':'zeta(3)'},
                       'MacMahon_positive_coefficients':{str(k):str(v) for k,v in exact.macmahon_coefficients(10).items()}},
        'constant_order_identity':{'basis':['s','A','D','ell','C'],
                                    'terms':exact.poly_rows(exact.constant_order_identity()),
                                    'substitutions':{'B':'D+A/4','u1':'D/(2*s^2)'},
                                    'verified':True}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'data/certificates.json')
    args=parser.parse_args()
    try:
        expected=derive()
        same(expected,load_certificate(args.data))
        prefix=manuscript_prefix(ROOT/'Report181.tex')
        print(json.dumps({'status':'PASS','report':181,'ordinary_convolution_terms_checked':601,
                          'composition_terms_checked':19,'manuscript_prefix_terms_checked':prefix,
                          'h_coefficients_checked':10,'Edgeworth_orders_checked':[1,2],
                          'free_energy_positive_degree_checked':10,'constant_order_algebra_checked':True,
                          'pinned_references_checked':len(PINS),'standard_library_only':True,
                          'asymptotic_remainders_certified_by_code':False},sort_keys=True))
    except (ValueError,TypeError,KeyError,IndexError,OSError) as exc:
        print('VERIFICATION FAILED: '+str(exc),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    sys.exit(main())
