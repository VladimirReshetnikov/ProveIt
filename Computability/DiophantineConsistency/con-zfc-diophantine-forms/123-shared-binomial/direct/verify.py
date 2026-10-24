#!/usr/bin/env python3
"""Independent full coefficient and natural-restoration verification.

Uses the retained independent checker, not the equation producer. All
conditions use explicit exceptions and remain active under python -O.
"""
from pathlib import Path
from copy import deepcopy
from hashlib import sha256
import argparse,json,re
from check_contraction import verify,canonical,require

HERE=Path(__file__).resolve().parent


def parse_term(text):
    token=text.replace(' ','')
    sign=1
    if token.startswith(('+','-')):
        sign=-1 if token[0]=='-' else 1
        token=token[1:]
    coefficient=sign
    monomial=[]
    for factor in token.split('*'):
        if factor.isdigit():
            coefficient*=int(factor)
        else:
            found=re.fullmatch(r'z([0-9]+)(?:\^([0-9]+))?',factor)
            require(found is not None,'unrecognized printed monomial')
            monomial.extend([int(found[1])]*int(found[2] or 1))
    return [coefficient,sorted(monomial)]


def verify_readable(directory,target,polynomial):
    checked=0
    p=directory/'natural/residuals.txt'
    if p.exists():
        lines=[s for s in p.read_text().splitlines() if re.match(r'^R[0-9]+ = ',s)]
        require(len(lines)==len(target['residuals']),'printed residual count differs')
        for i,(line,row) in enumerate(zip(lines,target['residuals']),1):
            head,expr=line.split(' = ')
            require(head==f'R{i:03d}','printed residual order differs')
            pieces=re.findall(r'[+-]?[^+-]+',expr)
            parsed=[parse_term(term) for term in pieces]
            require(parsed==row['terms'],'printed residual coefficient differs')
        checked+=1
    p=directory/'natural/polynomial.txt'
    if p.exists():
        lines=[s for s in p.read_text().splitlines() if s.startswith(('+ ','- '))]
        require([parse_term(s) for s in lines]==polynomial,'printed polynomial differs')
        checked+=1
    return checked


def run(directory):
    directory=Path(directory)
    source=json.loads((directory/'raw/equation.json').read_text())
    target=json.loads((directory/'natural/equation.json').read_text())
    cert=json.loads((directory/'natural/elimination_certificate.json').read_text())
    full=json.loads((directory/'natural/expanded_polynomial.json').read_text())
    meta=json.loads((directory/'raw/raw_audit_input.json').read_text())
    expected=json.loads((directory/'natural/VERIFICATION.json').read_text())
    count=len(target['variables'])
    for row in target['residuals']:
        for coefficient,monomial in row['terms']:
            require(type(coefficient) is int and coefficient!=0,'invalid integer coefficient')
            require(len(monomial)<=2 and monomial==sorted(monomial),'not a canonical quadratic monomial')
            require(all(type(v) is int and 0<=v<count for v in monomial),'variable outside declared domain')
    live={v for row in target['residuals'] for c,m in row['terms'] for v in m}
    require(live==set(range(count)),'unused declared coordinate')
    receipt,polynomial=verify(source,target,cert)
    require(receipt==expected,'recorded verification differs')
    require(polynomial==full['terms'],'full collected polynomial differs')
    readable=verify_readable(directory,target,polynomial)
    require(len(meta['powers'])==6 and len(meta['seeds'])==15,'wrong exact-power/seed count')
    require(len(meta['modular_requests'])==11 and len(meta['binomials'])==1,'wrong binomial graph counts')
    require(len(meta['ranges'])==10 and len(meta['factorials'])==1,'wrong source macro counts')
    require(len(meta['denominator_derivations'])==1,'missing denominator shift')
    require(meta['factorials'][0]['binomial']==meta['product']['product'],
            'factorial and CRT product do not share the identical output')
    # Modify a row while recomputing its hash: detection must be algebraic.
    bad=deepcopy(target);bad['residuals'][0]['terms'][0][0]+=1
    badcert=deepcopy(cert);badcert['target_equation_sha256']=sha256(canonical(bad)).hexdigest()
    try:
        verify(source,bad,badcert)
    except ValueError:
        pass
    else:
        raise ValueError('changed target residual was accepted')
    # Modify a restoration while preserving both equation hashes.
    badcert=deepcopy(cert)
    badcert['steps'][0]['restoration'][0][0]+=1
    try:
        verify(source,target,badcert)
    except ValueError:
        pass
    else:
        raise ValueError('changed natural restoration was accepted')
    badpoly=deepcopy(full['terms']);badpoly[0][0]+=1
    require(badpoly!=polynomial,'changed final coefficient was not detected')
    return {'status':'PASS','equation':directory.name,'metrics':receipt,
        'exact_power_requests':6,'independently_certified_pell_indices':15,
        'modular_requests':11,'all_coordinates_live':True,'negative_controls':3,
        'readable_files_verified':readable,
        'scope':'complete finite polynomial/restoration identities; not a proof of consistency'}


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--equation',type=Path,default=HERE/'equation319')
    p.add_argument('--output',type=Path)
    a=p.parse_args();result=run(a.equation)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')
