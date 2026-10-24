#!/usr/bin/env python3
"""Separate retained-wire sibling: two signs from exact shifted row bounds."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
PARENT=ROOT/'candidates/retained-radius-integers'
DEST=ROOT/'candidates/retained-radius-bounds'
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
ARCHIVE=REPO/'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
BASE='ConZFC_407_888_Quartics/code/integer_pipeline/'
CONFIGS=[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),
         ('support4_affine2',4,2),('support8_affine2',8,2)]


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()
def encoded(obj):return(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()


def bounds():
    one=[[1,[]]]
    return [dict(variable=4,lower=1,factor=one,rhs=[[1,[]],[1,[0]]],
                 row_combination=[dict(row=0,multiplier=one)]),
            dict(variable=5,lower=2,factor=one,rhs=[[1,[]],[1,[4]]],
                 row_combination=[dict(row=1,multiplier=one)]),
            dict(variable=644,lower=2,factor=[[2,[5]]],rhs=[[1,[]],[1,[5,5]],[1,[694]]],
                 row_combination=[dict(row=i,multiplier=[[c,m]])for i,c,m in
                                  [(644,1,[]),(643,1,[]),(642,1,[]),(640,-1,[]),(639,-1,[5]),(641,1,[])]]),
            dict(variable=917,lower=2,factor=one,rhs=[[-1,[]],[1,[644,644]]],
                 row_combination=[dict(row=i,multiplier=[[c,[]]])for i,c in [(853,-1),(852,-1),(598,1)]])]


def build():
    need(digest(ARCHIVE.read_bytes())==PIN,'reviewed engine ZIP')
    natural=json.loads((PARENT/'raw_natural.json').read_text());old=json.loads((PARENT/'domain_conversion.json').read_text())
    seeds=[i for i in old['positivity']['guard_indices']if i not in [644,917]]
    need(len(seeds)==159 and all(i in old['positivity']['guard_indices']for i in [644,917]),'exact two guard deletion')
    cert=dict(schema='row_ideal_shifted_bounds_v1',seed_indices=seeds,bound_steps=bounds(),
              sign_steps=[s for s in old['positivity']['proof_steps']if s['variable']not in [4,5]])
    signed=deepcopy(natural);signed['domain']='unrestricted integers';signed.pop('metrics',None);guards=[]
    for v in seeds:
        a,b,c=range(len(signed['variables']),len(signed['variables'])+3)
        signed['variables'] += [dict(name=f'nonnegative.{v}.{s}',kind='integer_guard')for s in ['a','b','c']]
        signed['residuals'].append(dict(label=f'nonnegative.{v}',terms=[[1,[v]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]]))
        guards.append(dict(variable=v,auxiliary=[a,b,c]))
    cert['guards']=guards
    files={'guarded.json':encoded(signed),'bounds_certificate.json':encoded(cert)};census={};members={}
    with tempfile.TemporaryDirectory(prefix='retained-radius-bounds-')as tmp,zipfile.ZipFile(ARCHIVE)as z:
        code=Path(tmp)
        for member in z.namelist():
            if member.startswith(BASE)and member.endswith('.py'):
                data=z.read(member);(code/Path(member).name).write_bytes(data);members[member]=digest(data)
        sys.path.insert(0,str(code));import terminal_elimination as e
        for name,cap,affine in CONFIGS:
            child,projection,metrics=e.optimize(signed,max_support=cap,affine_support=affine)
            need(projection['unconstrained_removed']==[],'no free removal')
            census[name]=metrics
            for key,obj in [('equation.json',child),('elimination_certificate.json',projection),
                            ('expanded_polynomial.json',e.expand(child)),
                            ('BUILD.json',dict(metrics=metrics,projection=e.verify(signed,child,projection)))]:
                files[name+'/'+key]=encoded(obj)
    pins=dict(parent='candidates/retained-radius-integers',
              parent_files={n:digest((PARENT/n).read_bytes())for n in ['raw_natural.json','raw_polynomial.json','domain_conversion.json','PROOF.md','check.py']},
              engine_archive=str(ARCHIVE.relative_to(REPO)),engine_archive_sha256=PIN,
              arithmetic_source_members=members,
              inverse_checker='candidates/projected-radius-integers/check.py',
              inverse_checker_sha256=digest((ROOT/'candidates/projected-radius-integers/check.py').read_bytes()))
    files['PARENT_PINS.json']=encoded(pins);files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
                                    sha256={n:digest(d)for n,d in files.items()}))
    return files,census


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,census=build()
    for n,data in files.items():
        p=DEST/n
        if args.check:need(p.read_bytes()==data,'byte-exact bounds sibling '+n)
        else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,metrics=census),indent=2))


if __name__=='__main__':main()
