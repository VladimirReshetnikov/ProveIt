#!/usr/bin/env python3
"""Actual raw export, fresh row signs, every integer inverse, all coefficients."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
BASE='ConZFC_407_888_Quartics/code/integer_pipeline/'
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
NAMES=['integer1742','integer1095','integer950','integer886','integer872']
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos
from review_quartics407888 import raw_export


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def load(name):return json.loads((HERE/name).read_text())


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def reject(thunk,label):
    try:thunk()
    except(ValueError,RuntimeError,IndexError,KeyError,TypeError):return label
    raise ValueError('corruption accepted '+label)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load('PARENT_PINS.json');parent=ROOT/pins['parent']
    for name,h in pins['parent_files'].items():need(digest((parent/name).read_bytes())==h,'entire frozen parent '+name)
    for path,key in [('independent_raw_export_tool','independent_raw_export_tool_sha256'),
                     ('independent_restoration_controls','independent_restoration_controls_sha256')]:
        need(digest((ROOT/pins[path]).read_bytes())==pins[key],'frozen independent checker '+pins[path])
    for name,h in load('BUILD.json')['sha256'].items():need(digest((HERE/name).read_bytes())==h,'complete generated packet '+name)
    raw=json.loads((parent/'both_source/raw_builder.json').read_text());natural=load('raw_natural.json')
    need(natural['domain']=='nonnegative integers'and natural['variables']==raw['variables']and
         natural['residuals']==[dict(label=r['label'],terms=r['terms'])for r in raw['rows']],'every raw natural row and coordinate')
    source667=json.loads((parent/'both_source/equation.json').read_text());ledger=json.loads((parent/'both_source/gate_ledger.json').read_text())
    rawcheck=raw_export(raw,ledger,source667)
    rawmetrics=full_sos(natural,load('raw_polynomial.json'))
    signed=load('guarded.json');conversion=load('domain_conversion.json');results={};controls=[]
    inverse=module('frozen_generic_integer_inverse_controls',ROOT/pins['independent_restoration_controls'])
    archive=REPO/pins['engine_archive'];need(digest(archive.read_bytes())==PIN==pins['engine_archive_sha256'],'whole reviewed engine archive')
    with tempfile.TemporaryDirectory(prefix='retained-radius-independent-')as tmp,zipfile.ZipFile(archive)as z:
        code=Path(tmp)
        for member,h in pins['arithmetic_source_members'].items():need(digest(z.read(member))==h,'exact arithmetic engine source')
        for name in ['verify_integer.py','verify_projection.py','independent_polynomial.py','audit_common_radix.py']:(code/name).write_bytes(z.read(BASE+name))
        sys.path.insert(0,str(code))
        from verify_integer import domain
        from verify_projection import verify
        proof=domain(natural,signed,conversion)
        need(proof['guarded_inputs']==161 and proof['derived_nonnegative']==1098,'fresh actual raw sign census')
        for name in NAMES:
            child=load(name+'/equation.json');cert=load(name+'/elimination_certificate.json');poly=load(name+'/expanded_polynomial.json')
            need(cert['unconstrained_removed']==[],'no unconstrained raw or sign variable removed')
            results[name]=dict(metrics=full_sos(child,poly),projection=verify(signed,child,cert),
                arbitrary_signed_restoration_controls=inverse.restoration_controls(signed,child,cert))
            if cert['steps']:
                bad=deepcopy(cert);bad['steps'][0]['restoration'][0][0]+=1
                controls.append(reject(lambda:verify(signed,child,bad),'changed integer restoration '+name))
        bad=deepcopy(conversion);bad['positivity']['proof_steps'][0]['rhs'][0][0]+=1
        controls.append(reject(lambda:domain(natural,signed,bad),'changed original raw sign row'))
        bad=deepcopy(conversion);bad['positivity']['proof_steps'].insert(1,deepcopy(bad['positivity']['proof_steps'][0]))
        controls.append(reject(lambda:domain(natural,signed,bad),'repeated sign inference'))
        bad=deepcopy(signed);bad['residuals'].pop()
        controls.append(reject(lambda:domain(natural,bad,conversion),'omitted seed guard'))
        child=load('integer1742/equation.json');bad=load('integer1742/expanded_polynomial.json');bad['terms'][0][0]+=1
        controls.append(reject(lambda:full_sos(child,bad),'altered coefficient at retained endpoint'))
    sign=conversion['positivity']['proof_steps']
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),raw_natural_metrics=rawmetrics,
        complete_raw_to_667_equivalence=rawcheck,actual_sign_certificate=proof,
        original_sign_rule_counts=dict(positive_monomials=sum(s['kind']!='affine_square'for s in sign),
                                       exact_affine_squares=sum(s['kind']=='affine_square'for s in sign)),
        variants=results,rejected_corruptions=controls,minimum_guard_claim=False,
        scope='Every retained raw row, total affine/square restoration, actual new guards/sign chain, complete signed inverse and coefficient lists. Natural source/refutation proof inherited. No Lean.')
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
