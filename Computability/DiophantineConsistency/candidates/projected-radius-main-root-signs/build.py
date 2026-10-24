#!/usr/bin/env python3
"""Complete79-guard904 integer quartic and fresh monic signed projections."""
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
NAMES=[('unprojected',0),('support4',4),('support8',8),('support16',16),('support32',32)]


def need(ok,text):
    if not ok:raise ValueError(text)


def load(path):return json.loads(path.read_text())
def digest(data):return sha256(data).hexdigest()
def encoded(v):return(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()


def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen input '+n)
    base=ROOT/pins['raw_foundation'];parent_dir=ROOT/pins['foundation967'];research=ROOT/pins['sign_research']
    body=load(base/'source/natural667.json');old=load(parent_dir/'domain_certificate.json');proof=load(research/'CERTIFICATE.json')
    remaining=[g for g in old['guards']if g['raw_variable']in proof['remaining_raw_guard_indices']]
    removed=[g for g in old['guards']if g['raw_variable']not in proof['remaining_raw_guard_indices']]
    need(len(remaining)==79 and removed==proof['pointwise_map']['missing_target_guard_records'],'exact79 kept/21 omitted guards')
    equation=deepcopy(body);equation['domain']='unrestricted integers'
    equation['variant']='mixed667_79_pointwise_main_root_modulus_sign_guards';equation.pop('metrics',None)
    guards=[]
    for j,g in enumerate(remaining):
        v=g['variable'];a,b,c=range(667+3*j,670+3*j)
        equation['variables'].extend(dict(kind='nonnegative_guard',name='guard.'+str(v)+'.'+s)for s in['a','b','c'])
        equation['residuals'].append(dict(label='guard.'+str(v),terms=[
            [1,[v]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]]))
        guards.append(dict(variable=v,raw_variable=g['raw_variable'],auxiliary=[a,b,c]))
    cert=dict(schema='mixed79_pointwise_guard_consequences_v1',guards=guards,
        seed_indices=[g['variable']for g in guards],removed_guard_records=removed,
        sign_certificate_sha256=digest((research/'CERTIFICATE.json').read_bytes()))
    slots={g['variable']:g['auxiliary']for g in old['guards']}
    bridge=dict(schema='pointwise904_to_literal967_v1',shared_body_coordinates=667,shared_body_rows=585,
        shared_guard_transfers=[dict(variable=g['variable'],raw_variable=g['raw_variable'],
            source_auxiliary=g['auxiliary'],target_auxiliary=slots[g['variable']])for g in guards],
        fresh_967_guard_records=removed,body_values_changed=0,
        statement='Reverse every signed projection first, then restore all raw wires over Z. The certified prefix/index/residue proof makes all21 omitted guard values nonnegative at the same body tuple. Copy all79 old guard triples and choose63 fresh Legendre witnesses into literal967. Reverse by forgetting exactly those21 triples.')
    files={'domain_certificate.json':encoded(cert),'BRIDGE967.json':encoded(bridge)};census={}
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    member='ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='mainroot904-produce-')as tmp:
        data=z.read(member);need(digest(data)==pins['read_source_members'][member],'literal signed optimizer')
        path=Path(tmp)/'terminal_elimination.py';path.write_bytes(data)
        spec=importlib.util.spec_from_file_location('mainroot904_signed_optimizer',path)
        engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
        polynomial=engine.expand(equation)
        equation['metrics']=dict(variables=len(equation['variables']),quadratic_rows=len(equation['residuals']),
            exact_degree=max(len(m)for c,m in polynomial['terms']),expanded_monomials=len(polynomial['terms']),
            max_abs_expanded_coefficient=max(abs(c)for c,m in polynomial['terms']))
        files['guarded.json']=encoded(equation)
        for name,cap in NAMES:
            child,projection,metrics=engine.optimize(equation,max_support=cap)
            need(projection['unconstrained_removed']==[],'every integer parent coordinate uniquely restored')
            review=engine.verify(equation,child,projection)
            for filename,value in[('equation.json',child),('elimination_certificate.json',projection),
                ('expanded_polynomial.json',engine.expand(child)),
                ('BUILD.json',dict(metrics=metrics,producer_internal_verification=review,support_cap=cap))]:
                files[name+'/'+filename]=encoded(value)
            census[name]=dict(metrics=child['metrics'],support_cap=cap,
                eliminated_coordinates=len(projection['steps']),unconstrained_removed=[])
    files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
        sha256={n:digest(d)for n,d in files.items()},scope='Complete904 integer quartic and fresh signed projections. The same body tuple reaches literal967 after63 fresh guard witnesses; no pointwise all-natural claim.'))
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
