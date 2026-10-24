#!/usr/bin/env python3
"""Independent original-row early sign,75 predicates,Z-inverses and quartics."""
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

def early_output_sign(data,raw,p):
    P,add,mul=p.poly,p.add,p.mul
    rows=[P(r['terms'])for r in raw['rows']]
    def collect(obj):
        q={}
        for t in obj['row_combination']:
            need(type(t['row'])is int and 0<=t['row']<len(rows),'actual original-row index')
            q=add(q,mul(P(t['multiplier']),rows[t['row']]))
        return q
    remainder=collect(data['original_source_cuts']['factorial_remainder_bound'])
    ceiling=collect(data['original_source_cuts']['factorial_ceiling'])
    need(remainder==P([[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]]),'entire original remainder-bound ideal')
    need(ceiling==P([[1,[87,91]],[-1,[93]],[-1,[95]]]),'entire original factorial ceiling ideal')
    combined=collect(data['combined']);target=P([[1,[93]],[-1,[87,94]],[-1,[87,95]],[1,[95]],[-1,[87]]])
    negative_ceiling={m:-c for m,c in ceiling.items()}
    need(combined==target==P(data['combined']['polynomial'])==add(mul({(87,):1},remainder),negative_ceiling),
         'complete unconditional early-output row combination')
    # N-2=f*r+(f-1)*s+f-2, with the three directly guarded values
    # F=f-2,r,s nonnegative. No C, N or gate sign is used.
    expression=P([[1,[87,94]],[1,[87,95]],[-1,[95]],[1,[87]],[-2,[]]])
    shifted=p.sub(expression,{87:{():2,(0,):1},94:{(1,):1},95:{(2,):1}})
    need(shifted==P([[1,[0]],[1,[0,1]],[1,[0,2]],[2,[1]],[1,[2]]])==P(data['N_minus_two_after_substitution'])
         and all(c>0 for c in shifted.values()),'exact nonnegative-coefficient proof of N>=2')
    return dict(complete_original_row_identities=3,combined_source_rows=len(data['combined']['row_combination']),
                recovered_raw_coordinate=93,recovered_lower_bound=2,intended_power_calls_used=0,
                proof_precedes_initial_prefix_closure=True)

def domain(eq,cert,family,old,oldcert,raw,body,initial):
    n=oldcert['baseline_body_variables'];nr=oldcert['baseline_body_rows'];indices=oldcert['baseline_raw_indices'];mp={v:i for i,v in enumerate(indices)}
    variables=raw['variables']if family=='raw'else body['variables']
    rows=[dict(label=r['label'],terms=r['terms'])for r in raw['rows']]if family=='raw'else body['residuals']
    need(old['variables'][:n]==variables and old['residuals'][:nr]==rows,'pinned76 body is original source verbatim')
    need(eq['domain']=='unrestricted integers'and eq['variables'][:n]==variables and eq['residuals'][:nr]==rows,'all original body metadata and coefficients unchanged')
    need(cert['baseline_body_variables']==n and cert['baseline_body_rows']==nr and cert['baseline_raw_indices']==indices,'whole body/raw-coordinate map')
    need(cert['removed_original_scalar_guard']==93 and cert['retained_parent_predicates']==75,'delete precisely one parent scalar predicate')
    predicates=[g['predicate']for g in oldcert['guards']if not(g['predicate']['kind']=='retained_scalar'and g['predicate']['raw_variables']==[93])]
    need(len(oldcert['guards'])==76 and len(predicates)==75,'exact75 remaining predicates')
    scalar={v['raw_variables'][0]for v in predicates if v['kind']=='retained_scalar'}
    need(len(scalar)==72 and len(initial)==61 and set(initial)-scalar=={93} and {94,95}<=scalar,
         'all60 other early signs retained and both direct remainder signs available')
    need([p for p in predicates if p['kind']!='retained_scalar']==[
        dict(kind='strict_common_V',raw_variables=[656],terms=[[1,[mp[656]]],[-1,[]]]),
        dict(kind='paired_index_slacks',raw_variables=[674,861],terms=[[1,[mp[674],mp[861]]]]),
        dict(kind='factorial_lower_bound',raw_variables=[87],terms=[[1,[mp[87]]],[-2,[]]])],
        'strictV/product/f>=2 predicates unchanged, including early f premise')
    need(len(eq['variables'])==n+225 and len(eq['residuals'])==nr+75 and len(cert['guards'])==75,'exact75-predicate dimensions, no extra wire')
    for j,(g,p)in enumerate(zip(cert['guards'],predicates)):
        a,b,c=range(n+3*j,n+3*j+3)
        need(g==dict(predicate=p,auxiliary=[a,b,c]),'every exact predicate and fresh triple')
        need(eq['variables'][a:c+1]==[dict(kind='nonnegative_guard',name='factorial_output_guard.'+str(j)+'.'+s)for s in['a','b','c']],'complete auxiliary metadata ownership')
        need(eq['residuals'][nr+j]==dict(label='factorial_output_guard.'+str(j),terms=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]),'every whole quadratic guard row')
    return dict(original_body_variables=n,original_body_rows=nr,predicates=75,retained_original_scalar_predicates=72,
        initial_direct_semantic_signs=60,initial_semantic_signs_after_independent_recovery=61,
        additional_defining_wires=0)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if(HERE/'MANIFEST.json').exists():
        seal=load(HERE/'MANIFEST.json')['files'];need(set(seal)=={str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()and p.name!='MANIFEST.json'},'closed full profile inventory')
        for n,h in seal.items():need(digest((HERE/n).read_bytes())==h,'sealed member '+n)
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen input '+n)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'producer pin')
    for n,h in build['files'].items():need(digest((HERE/n).read_bytes())==h,'whole generated profile '+n)
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json');body=load(ROOT/'candidates/projected-radius-mixed-bounds/source/natural667.json')
    restore=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_restoration.json');prior=load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    primitive=module('pinned_independent_raw_row_primitives',ROOT/'research/paired-index-guard-profile/check.py')
    fixtures=module('pinned_independent_signed_fixtures',ROOT/'candidates/projected-radius-integers/check.py')
    recovery_data=load(ROOT/'research/factorial-radius-output-sign/CERTIFICATE.json')
    recovery=early_output_sign(recovery_data,raw,primitive)
    mutations=[];bad=deepcopy(recovery_data);bad['combined']['row_combination'][0]['multiplier'][0][0]+=1
    mutations.append(reject('alter original early-output multiplier',lambda:early_output_sign(bad,raw,primitive)))
    bad=deepcopy(recovery_data);bad['N_minus_two_after_substitution'][0][0]+=1
    mutations.append(reject('alter early-output positivity coefficient',lambda:early_output_sign(bad,raw,primitive)))
    domains={};parents={}
    for family in['compact','raw']:
        p=ROOT/'research/factorial-radius-guard-profile'/family;old,oldcert=load(p/'parent.json'),load(p/'domain.json')
        eq=load(HERE/family/'parent.json');cert=load(HERE/family/'domain.json');parents[family]=eq;initial=prior['prefix_proof']['initial_semantic_guard_indices']
        domains[family]=domain(eq,cert,family,old,oldcert,raw,body,initial)
        bad=deepcopy(eq);bad['residuals'][-1]['terms'][1][0]=-1
        mutations.append(reject('weaken actual f-2 guard '+family,lambda:domain(bad,cert,family,old,oldcert,raw,body,initial)))
        bad=deepcopy(cert);bad['removed_original_scalar_guard']=94
        mutations.append(reject('omit necessary direct remainder sign '+family,lambda:domain(eq,bad,family,old,oldcert,raw,body,initial)))
    bridge=primitive.raw_compact_bijection(parents['raw'],parents['compact'],restore,'direct',raw['rows'])
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole arithmetic archive')
    results={}
    with tempfile.TemporaryDirectory(prefix='factorial75-independent-')as tmp,zipfile.ZipFile(archive)as z:
        for n,h in pins['members'].items():need(digest(z.read(n))==h,'whole pinned member '+n)
        for n in['verify_projection.py','independent_polynomial.py','audit_common_radix.py']:
            member=next(m for m in pins['members']if m.endswith('/'+n));(Path(tmp)/n).write_bytes(z.read(member))
        sys.path.insert(0,str(tmp));from verify_projection import verify
        for name,record in load(HERE/'CENSUS.json').items():
            parent=parents[name.split('/')[0]];out=load(HERE/name/'equation.json');cert=load(HERE/name/'projection.json');poly=load(HERE/name/'polynomial.json')
            need(cert['unconstrained_removed']==[]and out['metrics']==record['metrics'],'complete coordinate and metric ledger')
            results[name]=dict(projection=verify(parent,out,cert),full_quartic=full_sos(out,poly),
                              arbitrary_signed_restoration_fixtures=fixtures.restoration_controls(parent,out,cert))
            if cert['steps']:
                bad=deepcopy(cert);bad['steps'][0]['restoration'][0][0]+=1
                mutations.append(reject('change signed inverse '+name,lambda:verify(parent,out,bad)))
            bad=deepcopy(poly);bad['terms'][0][0]+=1
            mutations.append(reject('change complete quartic '+name,lambda:full_sos(out,bad)))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),early_source_sign_recovery=recovery,
        literal_domains=domains,raw_compact_integer_bijection=bridge,profiles=results,rejected_corruptions=mutations,
        source_pins={str(p.relative_to(ROOT)):digest(p.read_bytes())for p in[HERE/'README.md',HERE/'SOURCE_PINS.json',HERE/'BUILD.json',Path(__file__)]},
        scope='Actual75-predicate systems, independent original-row early sign before prefix closure, complete source/domain rows, unrestricted integer inverses first and full quartics. No global optimum, native/internal-ZFC/Lean claim.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations)),indent=2))
if __name__=='__main__':main()
