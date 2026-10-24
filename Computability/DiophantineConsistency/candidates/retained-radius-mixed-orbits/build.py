#!/usr/bin/env python3
"""Keep every raw coefficient, copy100 guards, produce low-height Z projections."""
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
CONFIGS=[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),
         ('support4_affine2',4,2),('support8_affine2',8,2)]


def need(ok,text):
    if not ok:raise ValueError(text)


def load(p):return json.loads(p.read_text())
def digest(d):return sha256(d).hexdigest()
def encoded(v):return(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()


def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen input '+n)
    base=ROOT/pins['raw_foundation'];target_dir=ROOT/pins['foundation967']
    raw=load(base/'source/raw_builder.json');body=load(base/'source/natural667.json')
    target=load(target_dir/'domain_certificate.json');restoration=load(base/'source/raw_restoration.json')
    identities={encoded(v):i for i,v in enumerate(raw['variables'])}
    retained=[identities[encoded(v)]for v in body['variables']]
    need(len(identities)==1259 and retained==restoration['retained_raw_indices'],'full metadata/raw restoration binding')
    need([g['raw_variable']for g in target['guards']]==[retained[g['variable']]for g in target['guards']],
         'every actual guard role is its literal raw coordinate')
    equation=dict(schema='quadratic_sum_squares_v1',domain='unrestricted integers',
        variant='retained1259_100_private_orbit_guards',variables=deepcopy(raw['variables']),
        residuals=[dict(label=r['label'],terms=r['terms'])for r in raw['rows']])
    guards=[]
    for j,g in enumerate(target['guards']):
        v=g['raw_variable'];a,b,c=range(1259+3*j,1262+3*j)
        equation['variables'].extend(dict(kind='nonnegative_guard',name='raw_guard.'+str(v)+'.'+s)for s in['a','b','c'])
        equation['residuals'].append(dict(label='raw_guard.'+str(v),terms=[
            [1,[v]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]]))
        guards.append(dict(raw_variable=v,contracted_variable=g['variable'],auxiliary=[a,b,c]))
    need(len(guards)==100,'complete100 guard set')
    cert=dict(schema='retained_raw100_guard_set_v1',guards=guards,
        raw_guard_indices=[g['raw_variable']for g in guards],retained_raw_indices=retained,
        literal967_domain_certificate_sha256=digest((target_dir/'domain_certificate.json').read_bytes()))
    omitted={item['raw_variable']for item in restoration['omitted']}
    row_map=[];next_row=0
    for row in raw['rows']:
        if row.get('gate')in omitted:row_map.append(None)
        else:row_map.append(next_row);next_row+=1
    need(next_row==585,'every raw nonzero row has exactly one literal body target')
    row_map.extend(range(585,685))
    bridge=dict(schema='literal1559_bijection_literal967_v1',raw_body_coordinates=1259,raw_body_rows=1177,
        target_body_coordinates=667,target_body_rows=585,retained_raw_indices=retained,
        source_retained_coordinates=retained+list(range(1259,1559)),
        raw_row_to_target_row=row_map,
        guard_transfers=[dict(raw_variable=g['raw_variable'],contracted_variable=g['contracted_variable'],
            source_auxiliary=g['auxiliary'],target_auxiliary=t['auxiliary'])for g,t in zip(guards,target['guards'])],
        affine_restoration_sha256=digest((base/'source/raw_restoration.json').read_bytes()),
        statement='Restrict raw body to its literal667 retained values and copy all100 guard triples. Reverse via all592 unique integer affine recipes and the same guard values/witnesses. No fresh witness or sign proof precedes the literal967 zero.')
    files={'domain_certificate.json':encoded(cert),'BRIDGE967.json':encoded(bridge)};census={}
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    member='ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='raw1559-produce-')as tmp:
        data=z.read(member);need(digest(data)==pins['read_source_members'][member],'literal signed optimizer')
        path=Path(tmp)/'terminal_elimination.py';path.write_bytes(data)
        spec=importlib.util.spec_from_file_location('raw1559_signed_optimizer',path)
        engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
        polynomial=engine.expand(equation)
        equation['metrics']=dict(variables=len(equation['variables']),quadratic_rows=len(equation['residuals']),
            exact_degree=max(len(m)for c,m in polynomial['terms']),expanded_monomials=len(polynomial['terms']),
            max_abs_expanded_coefficient=max(abs(c)for c,m in polynomial['terms']))
        files['guarded.json']=encoded(equation)
        for name,cap,affine in CONFIGS:
            child,projection,metrics=engine.optimize(equation,max_support=cap,affine_support=affine)
            need(projection['unconstrained_removed']==[],'every raw parent coordinate uniquely restored')
            review=engine.verify(equation,child,projection)
            for filename,value in[('equation.json',child),('elimination_certificate.json',projection),
                ('expanded_polynomial.json',engine.expand(child)),
                ('BUILD.json',dict(metrics=metrics,producer_internal_verification=review,support_cap=cap,affine_cap=affine))]:
                files[name+'/'+filename]=encoded(value)
            census[name]=dict(metrics=child['metrics'],support_cap=cap,affine_cap=affine,
                eliminated_coordinates=len(projection['steps']),unconstrained_removed=[])
    files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
        sha256={n:digest(d)for n,d in files.items()},scope='Complete raw1559 integer quartic and fresh low-height signed projections; exact integer bijection into frozen967 before any domain normalization.'))
    return files,census


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,census=generate()
    for n,data in files.items():
        path=HERE/n
        if args.check:need(path.read_bytes()==data,'entire deterministic artifact '+n)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,metrics={n:d['metrics']for n,d in census.items()}),indent=2))


if __name__=='__main__':main()
