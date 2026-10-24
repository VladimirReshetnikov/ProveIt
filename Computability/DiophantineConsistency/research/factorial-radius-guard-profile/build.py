#!/usr/bin/env python3
"""Fresh76-predicate profiles, preserving every original body coefficient."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];REPO=ROOT.parents[1]
CONFIGS={
 'compact':[('unprojected',0,None),('support4',4,None),('support8',8,None),('support16',16,None),('support32',32,None)],
 'raw':[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),('support4_affine2',4,2),
        ('support8_affine2',8,2),('support16_affine2',16,2),('support32_affine2',32,2),
        ('support8_affine3',8,3),('support16_affine3',16,3),('support32_affine3',32,3)]}
def need(b,s):
    if not b:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def digest(b):return sha256(b).hexdigest()
def encoded(v):return(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def module(n,p):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen source '+n)
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole archive')
    files={};census={}
    with tempfile.TemporaryDirectory(prefix='factorial76-profile-')as tmp,zipfile.ZipFile(archive)as z:
        for n,h in pins['members'].items():need(digest(z.read(n))==h,'whole arithmetic member '+n)
        n=next(n for n in pins['members']if n.endswith('/terminal_elimination.py'))
        f=Path(tmp)/'engine.py';f.write_bytes(z.read(n));engine=module('pinned_factorial76_optimizer',f)
        for family,configs in CONFIGS.items():
            predecessor=ROOT/'research/paired-index-guard-profile'/family/'direct'
            old=load(predecessor/'parent.json');old_domain=load(predecessor/'domain.json')
            n=old_domain['baseline_body_variables'];nr=old_domain['baseline_body_rows'];raw_indices=old_domain['baseline_raw_indices'];mp={v:i for i,v in enumerate(raw_indices)}
            eq=dict(schema='quadratic_sum_squares_v1',domain='unrestricted integers',variant='factorial_radius76_'+family,
                    variables=deepcopy(old['variables'][:n]),residuals=deepcopy(old['residuals'][:nr]))
            predicates=[g['predicate']for g in old_domain['guards']if g['predicate']['raw_variables']not in[[711],[779]]]
            need(len(predicates)==75,'delete exactly two local index bounds')
            predicates.append(dict(kind='factorial_lower_bound',raw_variables=[87],terms=[[1,[mp[87]]],[-2,[]]]))
            guards=[]
            for j,p in enumerate(predicates):
                a,b,c=range(len(eq['variables']),len(eq['variables'])+3)
                eq['variables'].extend(dict(kind='nonnegative_guard',name='factorial_radius_guard.'+str(j)+'.'+s)for s in['a','b','c'])
                eq['residuals'].append(dict(label='factorial_radius_guard.'+str(j),terms=deepcopy(p['terms'])+
                    [[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
                guards.append(dict(predicate=p,auxiliary=[a,b,c]))
            need(len(guards)==76,'complete76-predicate parent')
            files[family+'/parent.json']=encoded(eq)
            files[family+'/domain.json']=encoded(dict(baseline_body_variables=n,baseline_body_rows=nr,
                baseline_raw_indices=raw_indices,guards=guards,removed_raw_index_slacks=[711,779],new_affine_lower_bound=[87,2]))
            for name,cap,affine in configs:
                out,cert,metrics=engine.optimize(eq,max_support=cap,affine_support=affine)
                need(cert['unconstrained_removed']==[],'every deleted integer uniquely restored');engine.verify(eq,out,cert)
                path=family+'/'+name
                files[path+'/equation.json']=encoded(out);files[path+'/projection.json']=encoded(cert);files[path+'/polynomial.json']=encoded(engine.expand(out))
                census[path]=dict(metrics=out['metrics'],support_cap=cap,affine_cap=affine,
                    unique_signed_restorations=len(cert['steps']),unconstrained_removed=[])
                print(path,out['metrics']['variables'],out['metrics']['expanded_monomials'],out['metrics']['max_abs_expanded_coefficient'],flush=True)
    files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(generator_sha256=digest(Path(__file__).read_bytes()),
        files={n:digest(b)for n,b in files.items()},scope='Fresh76-predicate ordinary-source research profiles. No new native/internal-ZFC/Lean result.'))
    return files,census

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,census=generate()
    for n,b in files.items():
        p=HERE/n
        if args.check:need(p.read_bytes()==b,'complete deterministic profile '+n)
        else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
    print(json.dumps(dict(status='PASS',check=args.check,profiles=len(census)),indent=2))
if __name__=='__main__':main()
