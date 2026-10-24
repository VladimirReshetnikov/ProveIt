#!/usr/bin/env python3
"""No optimizer: literal76 predicates, complete signed inverses and quartics."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];REPO=ROOT.parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos
def need(b,s):
    if not b:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def digest(b):return sha256(b).hexdigest()
def module(n,p):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def reject(s,f):
    try:f()
    except(ValueError,RuntimeError,KeyError,IndexError,TypeError):return s
    raise ValueError('corruption accepted '+s)

def domain(eq,cert,family,old,oldcert,raw,body,restore,initial_guards):
    n=oldcert['baseline_body_variables'];nr=oldcert['baseline_body_rows'];indices=oldcert['baseline_raw_indices'];mp={v:i for i,v in enumerate(indices)}
    variables=raw['variables']if family=='raw'else body['variables']
    rows=[dict(label=r['label'],terms=r['terms'])for r in raw['rows']]if family=='raw'else body['residuals']
    need(old['variables'][:n]==variables and old['residuals'][:nr]==rows,'all pinned77 parent body rows/metadata are literal original source')
    need(eq['domain']=='unrestricted integers'and eq['variables'][:n]==variables and eq['residuals'][:nr]==rows,'full original body unchanged')
    need(cert['baseline_body_variables']==n and cert['baseline_body_rows']==nr and cert['baseline_raw_indices']==indices,'entire raw-coordinate binding')
    need(cert['removed_raw_index_slacks']==[711,779]and cert['new_affine_lower_bound']==[87,2],'exact source-domain replacement')
    predicates=[g['predicate']for g in oldcert['guards']if g['predicate']['raw_variables']not in[[711],[779]]]
    need(len(predicates)==75,'exact75 unchanged predicates')
    scalar=[p['raw_variables'][0]for p in predicates if p['kind']=='retained_scalar']
    need(len(scalar)==73 and set(initial_guards)<=set(scalar)and len(initial_guards)==61,'all61 early semantic premises preserved')
    need([p for p in predicates if p['kind']!='retained_scalar']==[
        dict(kind='strict_common_V',raw_variables=[656],terms=[[1,[mp[656]]],[-1,[]]]),
        dict(kind='paired_index_slacks',raw_variables=[674,861],terms=[[1,[mp[674],mp[861]]]])],
        'strictV and actual paired-slack product retained exactly')
    predicates.append(dict(kind='factorial_lower_bound',raw_variables=[87],terms=[[1,[mp[87]]],[-2,[]]]))
    need(len(eq['variables'])==n+228 and len(eq['residuals'])==nr+76 and len(cert['guards'])==76,'literal76-predicate dimensions, no extra wire')
    for j,(g,p)in enumerate(zip(cert['guards'],predicates)):
        a,b,c=range(n+3*j,n+3*j+3)
        need(g==dict(predicate=p,auxiliary=[a,b,c]),'every exact predicate/fresh triple')
        need(eq['variables'][a:c+1]==[dict(kind='nonnegative_guard',name='factorial_radius_guard.'+str(j)+'.'+s)for s in['a','b','c']],'all auxiliary metadata ownership')
        need(eq['residuals'][nr+j]==dict(label='factorial_radius_guard.'+str(j),terms=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]),'entire original-value quadratic guard row')
    return dict(original_body_variables=n,original_body_rows=nr,predicates=76,retained_scalar_predicates=73,
                unchanged_early_semantic_premises=61,new_affine_value=[87,2],additional_defining_wires=0)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if(HERE/'MANIFEST.json').exists():
        seal=load(HERE/'MANIFEST.json')['files']
        need(set(seal)=={str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()and p.name!='MANIFEST.json'},'closed profile file set')
        for n,h in seal.items():need(digest((HERE/n).read_bytes())==h,'closed profile member '+n)
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen input '+n)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'producer pin')
    for n,h in build['files'].items():need(digest((HERE/n).read_bytes())==h,'whole generated artifact '+n)
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    body=load(ROOT/'candidates/projected-radius-mixed-bounds/source/natural667.json')
    restore=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_restoration.json')
    prior=load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    primitive=module('pinned_independent_592_row_verifier',ROOT/'research/paired-index-guard-profile/check.py')
    fixtures=module('pinned_independent_integer_fixtures',ROOT/'candidates/projected-radius-integers/check.py')
    domains={};parents={};mutations=[]
    for family in['compact','raw']:
        p=ROOT/'research/paired-index-guard-profile'/family/'direct'
        old,oldcert=load(p/'parent.json'),load(p/'domain.json');eq=load(HERE/family/'parent.json');cert=load(HERE/family/'domain.json');parents[family]=eq
        initial=prior['prefix_proof']['initial_semantic_guard_indices']
        domains[family]=domain(eq,cert,family,old,oldcert,raw,body,restore,initial)
        bad=deepcopy(eq);bad['residuals'][-1]['terms'][1][0]=-1
        mutations.append(reject('weaken actual f-2 guard '+family,lambda:domain(bad,cert,family,old,oldcert,raw,body,restore,initial)))
        bad=deepcopy(cert);bad['removed_raw_index_slacks']=[674,861]
        mutations.append(reject('delete wrong local index bounds '+family,lambda:domain(eq,bad,family,old,oldcert,raw,body,restore,initial)))
    bridge=primitive.raw_compact_bijection(parents['raw'],parents['compact'],restore,'direct',raw['rows'])
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole arithmetic archive')
    results={}
    with tempfile.TemporaryDirectory(prefix='factorial76-independent-')as tmp,zipfile.ZipFile(archive)as z:
        for n,h in pins['members'].items():need(digest(z.read(n))==h,'pinned arithmetic member '+n)
        for n in['verify_projection.py','independent_polynomial.py','audit_common_radix.py']:
            member=next(m for m in pins['members']if m.endswith('/'+n));(Path(tmp)/n).write_bytes(z.read(member))
        sys.path.insert(0,str(tmp));from verify_projection import verify
        for name,record in load(HERE/'CENSUS.json').items():
            parent=parents[name.split('/')[0]];out=load(HERE/name/'equation.json');cert=load(HERE/name/'projection.json');poly=load(HERE/name/'polynomial.json')
            need(cert['unconstrained_removed']==[]and out['metrics']==record['metrics'],'complete coordinate/metrics ledger')
            results[name]=dict(projection=verify(parent,out,cert),full_quartic=full_sos(out,poly),
                arbitrary_signed_restoration_fixtures=fixtures.restoration_controls(parent,out,cert))
            if cert['steps']:
                bad=deepcopy(cert);bad['steps'][0]['restoration'][0][0]+=1
                mutations.append(reject('change signed inverse '+name,lambda:verify(parent,out,bad)))
            bad=deepcopy(poly);bad['terms'][0][0]+=1
            mutations.append(reject('change full quartic '+name,lambda:full_sos(out,bad)))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_domains=domains,raw_compact_integer_bijection=bridge,
        profiles=results,rejected_corruptions=mutations,
        source_pins={str(p.relative_to(ROOT)):digest(p.read_bytes())for p in[HERE/'README.md',HERE/'SOURCE_PINS.json',HERE/'BUILD.json',Path(__file__)]},
        scope='Actual76-predicate research systems, full original body/domain rows, unrestricted integer inverses first, complete quartic coefficients. Separately pinned ordinary factorial-radius proof is required. No global minimum, native/internal-ZFC/Lean result.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations)),indent=2))
if __name__=='__main__':main()
