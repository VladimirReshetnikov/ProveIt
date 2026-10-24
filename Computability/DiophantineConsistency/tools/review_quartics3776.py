#!/usr/bin/env python3
"""Inert authentication, complete polynomial expansion and sign-orbit controls."""
import argparse
from collections import Counter
from hashlib import sha256,sha1
import json
from pathlib import Path
import subprocess
import sys

from review_synchronized_certificates import load_archive,full_sos

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
ARCHIVE=REPO/'docs/incoming/ConZFC_Direct_Quartics_3776_3671_2026-10-23.zip'
PIN='91baf0ee4c8bf277f5caa2e735052474a68688557126463090db74e21063b7a7'
BASE='conzfc_signed_quartic/'


def need(ok,text):
    if not ok:raise RuntimeError(text)


def digest(raw):return sha256(raw).hexdigest()


def checked_sos(eq,poly):
    # Earlier data uses coefficient_height rather than the modern field name.
    e=dict(eq);e['metrics']=dict(eq['metrics'])
    if 'max_abs_expanded_coefficient'not in e['metrics']:e['metrics']['max_abs_expanded_coefficient']=e['metrics']['coefficient_height']
    return full_sos(e,poly)


def sign_orbits(source,cert):
    n=source['metrics']['core_variables'];nr=source['metrics']['core_rows']
    variables=source['variables'][:n];rows=source['residuals'][:nr]
    semantics={i for i,v in enumerate(variables)if v['kind']in('witness','outer')}
    guards=set(cert['guarded_coordinates']);pivots=set();row_checks=0
    for generator in cert['sign_symmetries']:
        p=generator['normalized_variable'];flips=set(generator['flip_variables'])
        need(len(flips)==len(generator['flip_variables'])and flips&semantics=={p},'single semantic sign pivot')
        need(p not in pivots and p not in guards,'independent unguarded pivots');pivots.add(p)
        for row in rows:
            need(len({sum(i in flips for i in m)%2 for c,m in row['terms']if c})==1,'whole residual sign automorphism')
            row_checks+=1
    basis={}
    for row in rows:
        masks=[]
        for c,m in row['terms']:
            mask=0
            for i in m:mask^=1<<i
            masks.append(mask)
        for mask in masks[1:]:
            v=mask^masks[0]
            while v:
                pivot=v.bit_length()-1
                if pivot in basis:v^=basis[pivot]
                else:basis[pivot]=v;break
    need(len(pivots)==110 and n-len(basis)==110,'exact full sign-kernel dimension')
    return dict(core_variables=n,core_rows=nr,independent_semantic_pivots=len(pivots),
                all_original_row_parities_checked=row_checks,full_sign_equation_rank=len(basis),
                full_sign_kernel_dimension=n-len(basis),guarded_pivots_unchanged=True,
                ordered_bound_steps=len(cert['bound_derivations']),guards=len(guards))


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--replay-receipt',type=Path);args=ap.parse_args()
    files=load_archive(ARCHIVE,PIN);get=lambda name:files[BASE+name];obj=lambda name:json.loads(get(name))
    manifest=0
    for line in get('SHA256SUMS').decode().splitlines():
        h,name=line.split('  ',1);need(digest(get(name))==h,'manifest member');manifest+=1
    parent=ROOT/'candidates/shared-crt-prime-lift';same=[]
    for name in obj('signed_quotients/source/SOURCE_PINS.json')['files']:
        raw=get('signed_quotients/source/upstream/'+name)
        need(raw==(parent/'source'/name).read_bytes(),'whole earlier reviewed source file '+name);same.append(name)
    for local,earlier in [('signed_quotients/source/natural_equation.json','affine/equation.json'),
                           ('signed_quotients/source/retained/equation.json','retained/equation.json')]:
        need(get(local)==(parent/earlier).read_bytes(),'complete exact natural parent '+earlier)
    calibration=[]
    for r in obj('source_calibration/SOURCE_URLS.json')['files']:
        raw=get('source_calibration/'+r['file']);git=subprocess.check_output(['git','show',r['commit']+':'+r['path']],cwd=REPO)
        need(raw==git and len(raw)==r['bytes']and digest(raw)==r['sha256'],'actual calibration Git bytes')
        need(sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==r['git_blob_sha1'],'actual Git blob ID')
        calibration.append(dict(file=r['file'],commit=r['commit'],path=r['path']))
    metrics={name:checked_sos(obj(path+'/equation.json'),obj(path+'/expanded_polynomial.json'))for name,path in
        [('main3776','equations/main'),('fewer3671','equations/fewer_variables'),
         ('retained7058','guard_minimization/retained_candidate'),('affine4879','guard_minimization/candidate')]}
    orbits={name:sign_orbits(obj('signed_quotients/'+source+'/equation.json'),obj('guard_minimization/'+target+'/guard_certificate.json'))for name,source,target in
            [('affine','candidate','candidate'),('retained','retained_candidate','retained_candidate')]}
    replay=None
    if args.replay_receipt:
        replay=json.loads(args.replay_receipt.read_text())
        need(replay['status']=='PASS'and replay['python_optimization']==sys.flags.optimize,'fresh full matching replay')
        need(replay['release_files_authenticated']==100 and len(replay['stages'])==12,'complete delivered stages')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),archive_sha256=PIN,
        manifest_members=manifest,whole_prior_source_files=same,whole_prior_natural_equations=2,
        exact_git_calibration_sources=calibration,metrics=metrics,whole_row_sign_orbit_checks=orbits,
        full_delivery_replay=replay,
        final_elimination_heuristic_rerun=False,
        scope='Complete old quartics, source identity and diagonal sign controls. Full independent elimination/bound replays supplied separately; universal review in PROPOSAL_REVIEW_QUARTICS3776.md. No Lean.')
    out=ROOT/('PROPOSAL_REVIEW_QUARTICS3776_OPTIMIZED.json'if sys.flags.optimize else'PROPOSAL_REVIEW_QUARTICS3776.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',metrics=metrics,orbits=orbits,full_replay_attached=replay is not None),indent=2))


if __name__=='__main__':main()
