#!/usr/bin/env python3
"""Profile literal paired guards using a pinned integral monic optimizer.

No source, metadata, arithmetic proof or frozen packet is modified.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
CONFIGS={
    'compact':[('unprojected',0,None),('support4',4,None),('support8',8,None),
               ('support16',16,None),('support32',32,None)],
    'raw':[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),
           ('support4_affine2',4,2),('support8_affine2',8,2)]}

def need(b,s):
    if not b:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def digest(b):return sha256(b).hexdigest()
def encoded(v):return (json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def module(n,p):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole pinned source '+n)
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    compact=load(ROOT/'candidates/projected-radius-mixed-bounds/source/natural667.json')
    restore=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_restoration.json')
    old=load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    proof=load(ROOT/'research/paired-index-guards/LOCAL_FACTORIAL_CERTIFICATE.json')
    retained=restore['retained_raw_indices'];oldguards=old['guards']
    need(len(retained)==667 and len(raw['variables'])==1259,'baseline dimensions')
    need([raw['variables'][i]for i in retained]==compact['variables'],'same literal metadata')
    keep=[g['raw_variable']for g in oldguards if g['raw_variable']not in[674,861,1214]]
    need(sorted(keep)==proof['retained_scalar_guards'] and len(keep)==75,'exact retained75 predicates')
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole optimizer archive')
    files={};census={}
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='paired-guard-profile-')as tmp:
        for n,h in pins['members'].items():need(digest(z.read(n))==h,'whole member '+n)
        member=next(n for n in pins['members']if n.endswith('/terminal_elimination.py'))
        path=Path(tmp)/'terminal_elimination.py';path.write_bytes(z.read(member))
        engine=module('pinned_paired_guard_optimizer',path)
        for family,configs in CONFIGS.items():
            if family=='raw':
                variables=raw['variables'];rows=[dict(label=r['label'],terms=r['terms'])for r in raw['rows']]
                mp={i:i for i in range(1259)}
            else:variables=compact['variables'];rows=compact['residuals'];mp={v:i for i,v in enumerate(retained)}
            for mode in['direct','wire']:
                eq=dict(schema='quadratic_sum_squares_v1',domain='unrestricted integers',
                        variant='paired77_'+family+'_'+mode,variables=deepcopy(variables),residuals=deepcopy(rows))
                if mode=='wire':
                    wire=len(eq['variables']);eq['variables'].append(dict(kind='gate',name='paired_index.product_wire'))
                    eq['residuals'].append(dict(label='paired_index.product_definition',terms=[[1,[wire]],[-1,[mp[674],mp[861]]]]))
                predicates=[dict(kind='retained_scalar',raw_variables=[v],terms=[[1,[mp[v]]]])for v in keep]
                predicates.append(dict(kind='strict_common_V',raw_variables=[656],terms=[[1,[mp[656]]],[-1,[]]]))
                predicates.append(dict(kind='paired_index_slacks',raw_variables=[674,861],
                    terms=[[1,[mp[674],mp[861]]]]if mode=='direct'else[[1,[wire]]]))
                guards=[]
                for j,p in enumerate(predicates):
                    a,b,c=range(len(eq['variables']),len(eq['variables'])+3)
                    eq['variables'].extend(dict(kind='nonnegative_guard',name='paired_guard.'+str(j)+'.'+s)for s in['a','b','c'])
                    eq['residuals'].append(dict(label='paired_guard.'+str(j),terms=deepcopy(p['terms'])+
                        [[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
                    guards.append(dict(predicate=p,auxiliary=[a,b,c]))
                need(len(guards)==77,'exact77 fresh predicate triples')
                prefix=family+'/'+mode
                files[prefix+'/parent.json']=encoded(eq)
                files[prefix+'/domain.json']=encoded(dict(baseline_body_variables=len(variables),baseline_body_rows=len(rows),
                    baseline_raw_indices=list(range(1259))if family=='raw'else retained,guards=guards,
                    product_wire=wire if mode=='wire'else None))
                for name,cap,affine in configs:
                    out,cert,metrics=engine.optimize(eq,max_support=cap,affine_support=affine)
                    need(cert['unconstrained_removed']==[],'all deleted variables have unique signed restorations')
                    engine.verify(eq,out,cert)
                    path=prefix+'/'+name
                    files[path+'/equation.json']=encoded(out)
                    files[path+'/projection.json']=encoded(cert)
                    files[path+'/polynomial.json']=encoded(engine.expand(out))
                    census[path]=dict(metrics=out['metrics'],support_cap=cap,affine_cap=affine,
                        unique_signed_restorations=len(cert['steps']),unconstrained_removed=[])
                    print(path, out['metrics']['variables'],out['metrics']['expanded_monomials'],
                          out['metrics']['max_abs_expanded_coefficient'],flush=True)
    files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(generator_sha256=digest(Path(__file__).read_bytes()),
        files={n:digest(b)for n,b in files.items()},scope='Actual77-guard ordinary-source research profiles; all original body metadata fixed. No native/internal-ZFC/Lean calibration theorem.'))
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
