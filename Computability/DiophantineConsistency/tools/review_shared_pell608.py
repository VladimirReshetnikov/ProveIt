#!/usr/bin/env python3
"""Inert-source, factorial-radius and full-polynomial audit of the 608 release."""
import argparse
import ast
from fractions import Fraction
from hashlib import sha256,sha1
import json
from math import comb,factorial
from pathlib import Path
import subprocess
import sys
import zipfile

from review_synchronized_certificates import full_sos,load_archive

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
ARCHIVE=REPO/'docs/incoming/ConZFC_Shared_Pell_608_2026-10-23.zip'
SHA='7782ba5510499c8925e3ca6895dc6ac71ecc6ea7cd85727fc95f6dc760dbdcc2'
PREFIX='con-zfc-shared-pell-2026-10-23/'


def need(ok,text):
    if not ok:raise RuntimeError(text)


def factorial_controls():
    pairs=ratio_bounds=completeness=0
    for n in range(21):
        F=factorial(n)
        values=range(F+3)if n<=8 else sorted({0,1,2,F//2}|set(range(F-5,F+6)))
        for f in values:
            rho=f*n*n;C=comb(rho+n,n);P=(rho+1)**n
            ceiling=(P+C-1)//C
            need((ceiling==f)==(f==F),'unique factorial fixed point including zero output')
            if n>=1 and f>=1:
                need(P<=F*C and 2*f*P>F*C*(2*f-1),'exact upper/strict lower ratio bounds')
                ratio_bounds+=1
            pairs+=1
        rho=F*n*n;C=comb(rho+n,n);P=(rho+1)**n
        r=P+C-F*C-1;s=C-r-1
        need(r>=0 and s>=0 and P+C==F*C+r+1 and C==r+s+1,'fresh natural ceiling witnesses')
        completeness+=1
    n,f=4,23;rho=f*n;C=comb(rho+n,n);P=(rho+1)**n
    need((P+C-1)//C==f and f!=factorial(n),'linear-radius negative control')
    return dict(candidate_pairs=pairs,strict_ratio_bounds=ratio_bounds,
                factorial_completeness_cases=completeness,largest_n=20,
                full_output_ranges_through_n=8,
                unsafe_linear_radius_false_fixed_point=dict(n=4,candidate=23,true_factorial=24))


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--replay-receipt',type=Path);args=ap.parse_args()
    files=load_archive(ARCHIVE,SHA);get=lambda p:files[PREFIX+p];obj=lambda p:json.loads(get(p))
    checked=0
    for line in get('MANIFEST.sha256').decode().splitlines():
        digest,name=line.split('  ',1);need(sha256(get(name)).hexdigest()==digest,'manifest actual bytes');checked+=1
    inherited=obj('provenance/inherited/CALIBRATION_PINS.json');git=[];omitted=[]
    for item in inherited['files']:
        name='provenance/inherited/'+item['local_file']
        if PREFIX+name not in files:omitted.append(item['local_file']);continue
        raw=get(name);blob=subprocess.check_output(['git','show',inherited['commit']+':'+item['repository_path']],cwd=REPO)
        need(raw==blob and sha256(raw).hexdigest()==item['sha256'],'copied exact logical Git source')
        git.append(item['repository_path'])
    need(omitted==['affine_shared_step.json'],'only unused expanded row table absent')
    parent=REPO/'docs/incoming/ConZFC_Shared_Certificates_2026-10-24.zip'
    need(sha256(parent.read_bytes()).hexdigest()=='61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1','immediate original archive')
    with zipfile.ZipFile(parent)as z:
        need(get('provenance/inherited/original_direct_calculus.py')==z.read('con_zfc_shared_certificates/direct/direct_calculus.py'),'full original calculus source')
        need(get('src/wire_eliminated_source.json')==z.read('con_zfc_shared_certificates/direct/wire_eliminated_source.json'),'full original source JSON')
    old=ast.parse(get('provenance/inherited/original_direct_calculus.py'));new=ast.parse(get('src/direct_calculus.py'));found=0
    for n in ast.walk(old):
        if isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='rows'and isinstance(n.value,ast.List)and len(n.value.elts)==4:
            n.value.elts=[n.value.elts[0],n.value.elts[2]];found+=1
    need(found==1 and ast.dump(old)==ast.dump(new),'source changed only two beta remainder rows')
    mraw=get('provenance/mathlib/PellMatiyasevic.lean');pins=obj('provenance/SOURCE_PINS.json')['mathlib_pell']
    need(sha256(mraw).hexdigest()==pins['sha256'],'actual bundled Mathlib SHA')
    adjusted=mraw[:-1]
    need(mraw.endswith(b'\n\n')and sha1(b'blob '+str(len(adjusted)).encode()+b'\0'+adjusted).hexdigest()==pins['github_blob'],'Mathlib Git source plus exactly one trailing LF')
    metrics={name:full_sos(obj(path+'/equation.json'),obj(path+'/expanded_polynomial.json'))for name,path in
             [('natural608','artifacts/natural'),('integer1685','artifacts/natural/integer')]}
    raw=obj('artifacts/natural/raw_builder.json')
    need(len(raw['powers'])==25 and len(raw['pell_indices'])==20,'actual power/group counts')
    replay=None
    if args.replay_receipt:
        replay=json.loads(args.replay_receipt.read_text())
        need(replay['status']=='PASS'and replay['optimized_python']==bool(sys.flags.optimize)and replay['byte_exact_rebuilt_artifacts']==9 and replay['rejected_corruption_controls']==8,'fresh full release replay')
        need(replay['literal_interface_rows_checked']==221,'all concrete semantic interfaces')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),archive_sha256=SHA,
        manifest_files=checked,exact_git_calibration_sources=git,omitted_unused_expanded_table=omitted,
        exact_original_source_and_two_beta_row_projection=True,
        mathlib_copy_has_one_additional_trailing_LF=True,
        metrics=metrics,power_calls=25,exponent_groups=20,
        independent_factorial_radius_controls=factorial_controls(),full_delivery_replay=replay,
        scope='Complete source authentication, exact SOS coefficients and factorial-radius controls. Ordinary unbounded review in PROPOSAL_REVIEW_SHARED_PELL_608.md; no Lean/internal-ZFC proof.')
    out=ROOT/('PROPOSAL_REVIEW_SHARED_PELL_608_OPTIMIZED.json'if sys.flags.optimize else'PROPOSAL_REVIEW_SHARED_PELL_608.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',metrics=metrics,factorial_controls=result['independent_factorial_radius_controls'],full_replay_attached=replay is not None),indent=2))


if __name__=='__main__':main()
