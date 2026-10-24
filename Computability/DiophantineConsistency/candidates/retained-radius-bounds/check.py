#!/usr/bin/env python3
"""Independent original-row ideal/bound, sign, inverse and full-SOS checks."""
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
NAMES=['retained','support2_affine1','support2_affine2','support4_affine2','support8_affine2']
BASE='ConZFC_407_888_Quartics/code/integer_pipeline/'
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()
def load(n):return json.loads((HERE/n).read_text())


def poly(terms):
    out={}
    for c,m in terms:
        need(type(c)is int and all(type(i)is int and i>=0 for i in m),'integer polynomial')
        k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return{m:c for m,c in out.items()if c}


def add(a,b,scale=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+scale*c
    return{m:c for m,c in out.items()if c}


def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return{m:c for m,c in out.items()if c}


def nonnegative(p,known,strict=False):
    shifted={}
    for m,c in p.items():
        term={():c}
        for v in m:
            atom={(v,):1}
            if known.get(v,0):atom[()]=known[v]
            term=mul(term,atom)
        shifted=add(shifted,term)
    need(all(c>0 for c in shifted.values()),'nonnegative shifted coefficients')
    need(all(m.count(v)%2==0 or v in known for m in shifted for v in set(m)),'shifted odd-coordinate signs')
    if strict:need(shifted.get((),0)>0,'strict shifted constant')
    return shifted


def domain(natural,signed,cert,old):
    n=len(natural['variables']);nr=len(natural['residuals']);seeds=cert['seed_indices']
    need(seeds==[v for v in old['positivity']['guard_indices']if v not in[644,917]],'exact inherited seeds minus A,D')
    need(len(seeds)==159 and len(set(seeds))==159,'159 unique seeds')
    need(signed['domain']=='unrestricted integers','integer domain')
    need(signed['variables'][:n]==natural['variables']and signed['residuals'][:nr]==natural['residuals'],'whole original prefix')
    guards=cert['guards'];need([g['variable']for g in guards]==seeds,'guard coverage')
    need(len(signed['variables'])==n+3*len(seeds)and len(signed['residuals'])==nr+len(seeds),'exact guard dimensions')
    for j,g in enumerate(guards):
        a,b,c=n+3*j,n+3*j+1,n+3*j+2;v=g['variable']
        need(g['auxiliary']==[a,b,c],'fresh private guard')
        need(poly(signed['residuals'][nr+j]['terms'])=={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'exact guard row')
    known={i:0 for i in seeds};bound_results=[]
    for step in cert['bound_steps']:
        v=step['variable'];lower=step['lower'];factor=poly(step['factor']);rhs=poly(step['rhs'])
        need(type(v)is int and 0<=v<n and v not in known,'new bound target')
        need(type(lower)is int and lower>=1,'positive integer lower bound')
        need(all(0<=i<n and i!=v for p in[factor,rhs]for m in p for i in m),'bound target absent from factor/RHS')
        target=add(mul({(v,):1},factor),rhs,-1);identity={}
        for item in step['row_combination']:
            i=item['row'];need(type(i)is int and 0<=i<nr,'original ideal-row index')
            multiplier=poly(item['multiplier'])
            need(all(i<n for m in multiplier for i in m),'ideal multiplier indices')
            identity=add(identity,mul(multiplier,poly(natural['residuals'][i]['terms'])))
        need(identity==target,'exact original-row ideal identity')
        positive_factor=nonnegative(factor,known,True)
        gap=add(rhs,factor,-(lower-1));positive_gap=nonnegative(gap,known,True)
        # If x <= lower-1, positive factor forces x*factor <=
        # (lower-1)*factor < RHS, contradicting the exact identity.
        known[v]=lower
        bound_results.append(dict(variable=v,lower=lower,original_rows=len(step['row_combination']),
                                  shifted_factor=[[c,list(m)]for m,c in sorted(positive_factor.items())],
                                  shifted_gap=[[c,list(m)]for m,c in sorted(positive_gap.items())]))
    need(cert['sign_steps']==[s for s in old['positivity']['proof_steps']if s['variable']not in[4,5]],'entire remaining original sign schedule')
    square_count=0
    for s in cert['sign_steps']:
        v=s['variable'];c=s['coefficient'];rhs=poly(s['rhs'])
        need(type(c)is int and c>0 and 0<=v<n and v not in known,'new original-row sign')
        need(all(0<=i<n and i!=v for m in rhs for i in m),'sign operand indices')
        expected=add({(v,):c},rhs,-1);row=poly(natural['residuals'][s['row']]['terms'])
        need(row==expected or row=={m:-a for m,a in expected.items()},'exact original sign row')
        if s.get('kind')=='affine_square':
            root=poly(s['square_root'])
            need(all(len(m)<=1 and all(0<=i<n and i!=v for i in m)for m in root),'affine square coordinates')
            need(mul(root,root)==rhs,'full affine square identity');square_count+=1
        else:
            need(all(a>0 for a in rhs.values()),'positive sign coefficients')
            need(all(m.count(i)%2==0 or i in known for m in rhs for i in set(m)),'ordered sign dependencies')
        known[v]=0
    need(set(known)==set(range(n)),'all original natural coordinates recovered')
    return dict(status='PASS',seed_count=len(seeds),derived_coordinates=n-len(seeds),
                shifted_bound_steps=bound_results,remaining_monomial_signs=len(cert['sign_steps'])-square_count,
                remaining_affine_squares=square_count,integer_variables=len(signed['variables']))


def reject(f,label):
    try:f()
    except(ValueError,RuntimeError,KeyError,IndexError,TypeError):return label
    raise ValueError('accepted mutation '+label)


def module(n,p):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load('PARENT_PINS.json');parent=ROOT/pins['parent']
    for n,h in pins['parent_files'].items():need(digest((parent/n).read_bytes())==h,'immutable parent '+n)
    for n,h in load('BUILD.json')['sha256'].items():need(digest((HERE/n).read_bytes())==h,'complete generated file '+n)
    need(digest((ROOT/pins['inverse_checker']).read_bytes())==pins['inverse_checker_sha256'],'independent inverse control source')
    natural=json.loads((parent/'raw_natural.json').read_text());old=json.loads((parent/'domain_conversion.json').read_text())
    signed=load('guarded.json');cert=load('bounds_certificate.json');proof=domain(natural,signed,cert,old)
    mutations=[]
    bad=deepcopy(cert);bad['bound_steps'][2]['row_combination'][4]['multiplier']=[[-1,[]]]
    mutations.append(reject(lambda:domain(natural,signed,bad,old),'changed nonconstant ideal multiplier'))
    bad=deepcopy(cert);bad['bound_steps'][1]['lower']=1
    mutations.append(reject(lambda:domain(natural,signed,bad,old),'only n>=1 available to A bound'))
    bad=deepcopy(cert);bad['bound_steps'][2]['lower']=3
    mutations.append(reject(lambda:domain(natural,signed,bad,old),'unsupported A>=3'))
    bad=deepcopy(cert);bad['bound_steps'][2],bad['bound_steps'][3]=bad['bound_steps'][3],bad['bound_steps'][2]
    mutations.append(reject(lambda:domain(natural,signed,bad,old),'D bound before A bound'))
    bad=deepcopy(cert);bad['sign_steps'][0]['rhs'][0][0]+=1
    mutations.append(reject(lambda:domain(natural,signed,bad,old),'changed original sign row'))
    bad=deepcopy(signed);bad['residuals'].pop()
    mutations.append(reject(lambda:domain(natural,bad,cert,old),'omitted seed guard'))
    archive=REPO/pins['engine_archive'];need(digest(archive.read_bytes())==PIN==pins['engine_archive_sha256'],'reviewed whole archive')
    results={};inverse=module('independent_complete_inverse_controls',ROOT/pins['inverse_checker'])
    with tempfile.TemporaryDirectory(prefix='independent-retained-bounds-')as tmp,zipfile.ZipFile(archive)as z:
        code=Path(tmp)
        for member,h in pins['arithmetic_source_members'].items():need(digest(z.read(member))==h,'pinned arithmetic source')
        for n in ['verify_projection.py','independent_polynomial.py','audit_common_radix.py']:(code/n).write_bytes(z.read(BASE+n))
        sys.path.insert(0,str(code));from verify_projection import verify
        for name in NAMES:
            child=load(name+'/equation.json');projection=load(name+'/elimination_certificate.json')
            need(projection['unconstrained_removed']==[],'no unconstrained deletion')
            results[name]=dict(metrics=full_sos(child,load(name+'/expanded_polynomial.json')),
                               projection=verify(signed,child,projection),signed_restoration_controls=inverse.restoration_controls(signed,child,projection))
            if projection['steps']:
                bad=deepcopy(projection);bad['steps'][0]['restoration'][0][0]+=1
                mutations.append(reject(lambda:verify(signed,child,bad),'changed signed inverse '+name))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),actual_row_domain_certificate=proof,
                variants=results,rejected_corruptions=mutations,
                scope='Exact original-row ideal identities, shifted strict bounds, all guards/signs, every signed inverse and full quartic. Natural source proof inherited. No Lean.')
    s=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(s)
    print(s,end='')


if __name__=='__main__':main()
