#!/usr/bin/env python3
"""No optimizer imported: literal sign rows, all guards, reverse integer maps."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
CONFIGS=['integer891','integer865','integer863','integer862']
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
BASE='ConZFC_407_888_Quartics/code/integer_pipeline/'
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def load(name):return json.loads((HERE/name).read_text())


def evaluate(terms,values):
    out=0
    for c,m in terms:
        for i in m:c*=values[i]
        out+=c
    return out


def restoration_controls(parent,child,cert):
    count=len(parent['variables']);tests=0
    for seed in range(3):
        values=[None]*count
        for i,v in enumerate(cert['retained_original_variables']):values[v]=((i+2)*5+seed)%7-3
        for step in reversed(cert['steps']):
            need(all(values[i]is not None for c,m in step['restoration']for i in m),'all restoration operands already recovered')
            values[step['variable']]=evaluate(step['restoration'],values)
        need(all(v is not None for v in values),'entire integer parent recovered')
        remaining=cert['retained_original_rows']
        for j,rid in enumerate(remaining):
            sub=[values[v]for v in cert['retained_original_variables']]
            need(evaluate(parent['residuals'][rid]['terms'],values)==evaluate(child['residuals'][j]['terms'],sub),'full signed surviving-row diagnostic')
        deleted=set(range(len(parent['residuals'])))-set(remaining)
        need(all(evaluate(parent['residuals'][rid]['terms'],values)==0 for rid in deleted),'all restored defining/zero rows, including guards')
        tests+=1
    return tests


def reject(thunk,label):
    try:thunk()
    except(ValueError,RuntimeError,KeyError,IndexError,TypeError):return label
    raise ValueError('corruption accepted '+label)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load('PARENT_PINS.json');raw=(ROOT/pins['parent_equation']).read_bytes()
    need(digest(raw)==pins['parent_equation_sha256'],'whole frozen natural parent')
    need(digest((ROOT/pins['parent_ordinary_proof']).read_bytes())==pins['parent_ordinary_proof_sha256'],'frozen ordinary source proof')
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==PIN==pins['archive_sha256'],'whole source archive')
    for name,h in load('BUILD.json')['sha256'].items():need(digest((HERE/name).read_bytes())==h,'complete generated file '+name)
    parent=json.loads(raw);signed=load('guarded.json');conversion=load('domain_conversion.json')
    results={};corruptions=[]
    with tempfile.TemporaryDirectory(prefix='projected-integer-independent-')as tmp,zipfile.ZipFile(archive)as z:
        code=Path(tmp)
        for name in ['verify_integer.py','verify_projection.py','independent_polynomial.py','audit_common_radix.py']:
            data=z.read(BASE+name);need(digest(data)==pins['arithmetic_source_members'][BASE+name],'pinned independent verifier')
            (code/name).write_bytes(data)
        for member,h in pins['arithmetic_source_members'].items():need(digest(z.read(member))==h,'all pinned arithmetic source members')
        sys.path.insert(0,str(code))
        from verify_integer import domain
        from verify_projection import verify
        domain_receipt=domain(parent,signed,conversion)
        need(domain_receipt['guarded_inputs']==161 and domain_receipt['derived_nonnegative']==506,'actual complete new sign census')
        for name in CONFIGS:
            child=load(name+'/equation.json');cert=load(name+'/elimination_certificate.json');poly=load(name+'/expanded_polynomial.json')
            need(cert['unconstrained_removed']==[],'no sign/free coordinate silently removed')
            results[name]=dict(projection=verify(signed,child,cert),metrics=full_sos(child,poly),
                               arbitrary_signed_restoration_controls=restoration_controls(signed,child,cert))
            bad=deepcopy(cert);bad['steps'][0]['restoration'][0][0]+=1
            corruptions.append(reject(lambda:verify(signed,child,bad),'changed restoration '+name))
        bad=deepcopy(conversion);bad['positivity']['proof_steps'][0]['rhs'][0][0]+=1
        corruptions.append(reject(lambda:domain(parent,signed,bad),'wrong original sign-row coefficient'))
        bad=deepcopy(conversion);bad['positivity']['proof_steps'].insert(1,deepcopy(bad['positivity']['proof_steps'][0]))
        corruptions.append(reject(lambda:domain(parent,signed,bad),'repeated sign inference'))
        bad=deepcopy(signed);bad['residuals'].pop()
        corruptions.append(reject(lambda:domain(parent,bad,conversion),'omitted guard equation'))
        child=load('integer862/equation.json');bad=load('integer862/expanded_polynomial.json');bad['terms'][0][0]+=1
        corruptions.append(reject(lambda:full_sos(child,bad),'changed final quartic coefficient'))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),actual_sign_certificate=domain_receipt,
                original_row_sign_rules={'positive_monomials':sum(s['kind']!='affine_square'for s in conversion['positivity']['proof_steps']),
                                         'exact_affine_squares':sum(s['kind']=='affine_square'for s in conversion['positivity']['proof_steps'])},
                variants=results,rejected_corruptions=corruptions,
                guard_minimum_claim=False,
                scope='Unrestricted-integer restoration first; original guards and actual-row sign chain recover naturals before macro semantics. No Lean/internalZFC theorem.')
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
