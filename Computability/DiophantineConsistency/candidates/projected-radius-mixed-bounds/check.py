#!/usr/bin/env python3
"""Independent original-row bounds, literal994 bridge and complete Z inverses."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
NAMES=['unprojected','support4','support8','support16','support32']
sys.path.insert(0,str(ROOT/'tools'))
from review_quartics407888 import raw_export
from review_synchronized_certificates import full_sos


def need(ok,text):
    if not ok: raise ValueError(text)


def digest(data): return sha256(data).hexdigest()
def load(name): return json.loads((HERE/name).read_text())
def encoded(value): return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj


def original_rows(raw,body,cert,mixed,b):
    restored,_=mixed.restoration(raw,body,cert,set())
    images=[];zero=0
    for row in raw['rows']:
        image={}
        for c,m in row['terms']:
            term={():c}
            for v in m: term=b.mul(term,restored[v])
            image=b.add(image,term)
        if image:
            images.append(dict(label=row['label'],terms=[[c,list(m)] for m,c in sorted(image.items())]))
        else: zero+=1
    need(images==body['residuals'] and len(images)==585 and zero==592,
         'every original1177 raw row is an exact retained row or zero over Z')
    need(restored[0]=={(0,):1} and restored[4]=={():1,(0,):1}
         and restored[5]=={():2,(0,):1} and restored[644]=={(294,):1}
         and restored[694]=={(326,):1} and restored[917]=={(461,):1},
         'literal restored t0,t,n,A,T,D identities')
    return dict(raw_rows=1177,retained_row_identities=585,zero_defining_row_identities=592,
                restored_coordinates=592,total_raw_coordinates=1259)


def bound_step(raw,step,known,b):
    v,L=step['variable'],step['lower'];F,G=b.poly(step['factor']),b.poly(step['rhs'])
    need(type(v)is int and 0<=v<1259 and v not in known and type(L)is int and L>=1,
         'fresh strict lower-bound target')
    need(all(0<=i<1259 and i!=v for p in [F,G] for m in p for i in m),'target-independent factor/RHS')
    expected=b.add(b.mul({(v,):1},F),G,-1);actual={}
    for item in step['row_combination']:
        i=item['row'];need(type(i)is int and 0<=i<1177,'original raw ideal row')
        multiplier=b.poly(item['multiplier'])
        need(all(0<=j<1259 for m in multiplier for j in m),'integer ideal multiplier')
        actual=b.add(actual,b.mul(multiplier,b.poly(raw['rows'][i]['terms'])))
    need(actual==expected,'complete original-row ideal identity')
    positiveF=b.nonnegative(F,known,True)
    positiveGap=b.nonnegative(b.add(G,F,-(L-1)),known,True)
    known[v]=L
    return dict(variable=v,lower=L,shifted_factor=[[c,list(m)]for m,c in sorted(positiveF.items())],
                shifted_gap=[[c,list(m)]for m,c in sorted(positiveGap.items())])


def domain(body,raw,signed,cert,old,b):
    ids={encoded(v):i for i,v in enumerate(raw['variables'])}
    need(len(ids)==1259,'unique full raw metadata')
    retained=[ids[encoded(v)]for v in body['variables']]
    need(retained==cert['retained_raw_indices'] and retained==sorted(set(retained))
         and len(retained)==667,'actual667 metadata subset')
    actual=[(i,retained[i])for i in [0,294,326,461]]
    need(actual==[(0,0),(294,644),(326,694),(461,917)],'actual t0,A,T,D identities')
    seeds=[v for v in old['guards']if retained[v]not in{644,917}]
    need(len(seeds)==107 and cert['seed_indices']==seeds and len(old['guards'])==109,
         'all107 guards are exactly old109 except the two derived values')
    need(cert['removed_guards']==[dict(variable=v,raw_variable=retained[v])for v in [294,461]],
         'only A,D guard omissions')
    need(cert['required_seed_identities']==[dict(variable=v,raw_variable=retained[v])for v in [0,326]]
         and {0,326}<=set(seeds),'actual t0/T prerequisites remain guarded')
    need(signed['domain']=='unrestricted integers' and signed['variables'][:667]==body['variables']
         and signed['residuals'][:585]==body['residuals'],'all original667/585 coefficients unchanged')
    need(len(signed['variables'])==988 and len(signed['residuals'])==692,'literal988/692 dimensions')
    need(len(cert['guards'])==107,'all107 private guard records')
    for j,v in enumerate(seeds):
        a,bb,c=range(667+3*j,670+3*j)
        need(cert['guards'][j]==dict(variable=v,raw_variable=retained[v],auxiliary=[a,bb,c]),'all guard coordinate identities')
        need(b.poly(signed['residuals'][585+j]['terms'])==
             {(v,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},'entire107 quadratic guard equations')
        need([signed['variables'][i]for i in [a,bb,c]]==[
            dict(kind='nonnegative_guard',name='guard.'+str(v)+'.'+s)for s in ['a','b','c']],
            'private guard metadata')
    # These bounds need only the two retained seeds, not the other105 signs.
    known={retained[v]:0 for v in [0,326]}
    bounds=[bound_step(raw,s,known,b)for s in cert['bound_steps']]
    need([(x['variable'],x['lower'])for x in bounds]==[(4,1),(5,2),(644,2),(917,2)],
         'exact four ordered t,n,A,D bounds')
    return dict(original_body_coordinates=667,original_body_rows=585,seed_count=107,
        integer_coordinates=988,quadratic_rows=692,required_seed_raw_indices=[0,694],
        strict_bound_steps=bounds,derived_contracted_nonnegative_values=[294,461])


def bridge994(body,signed,cert,old,foundation,bridge,mixed):
    mixed.guard_equation(body,foundation,old)
    retained=cert['retained_raw_indices'];positions={v:j for j,v in enumerate(old['guards'])}
    need(bridge['shared_body_coordinates']==667 and bridge['shared_body_rows']==585,
         'literal common585-row body')
    expected=[dict(variable=g['variable'],raw_variable=g['raw_variable'],source_auxiliary=g['auxiliary'],
        target_auxiliary=list(range(667+3*positions[g['variable']],670+3*positions[g['variable']])))
        for g in cert['guards']]
    need(bridge['shared_guard_transfers']==expected and len(expected)==107,'every exact old/new guard witness slot')
    fresh=[dict(variable=v,raw_variable=retained[v],target_auxiliary=list(range(
        667+3*positions[v],670+3*positions[v])))for v in [294,461]]
    need(bridge['new_994_guard_triples']==fresh,'precisely six fresh A/D witnesses')
    sources=[i for item in expected for i in item['source_auxiliary']]
    targets=[i for item in expected+fresh for i in item['target_auxiliary']]
    need(sorted(sources)==list(range(667,988)) and sorted(targets)==list(range(667,994)),
         'entire source and target auxiliary partition')
    return dict(source_integer_variables=988,target_integer_variables=994,copied_guard_triples=107,
        fresh_guard_triples=2,fresh_existential_integer_witnesses=6,
        target_A_guard_indices=[865,866,867],target_D_guard_indices=[934,935,936],
        theorem='An integer zero extends to literal994 by Legendre for A,D; every literal994 zero restricts by forgetting those two triples.')


def controls():
    # Diagnostics only. The universal guard equivalence is proved in PROOF.md.
    nonnegative=0
    for a in range(-5,6):
        for b in range(-5,6):
            for c in range(-5,6):
                need(a*a+b*b+c*(c+1)>=0,'all-sign local guard control');nonnegative+=1
    representations=0
    for x in range(129):
        need(any(a*a+b*b+c*(c+1)==x for a in range(12)for b in range(12)for c in range(12)),
             'small natural guard witness control');representations+=1
    return dict(all_sign_guard_cases=nonnegative,natural_guard_values=representations)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load('SOURCE_PINS.json')
    for n,p in pins['sources'].items():
        data=(HERE/'source'/n).read_bytes()
        need(digest(data)==p['sha256'] and data==(ROOT/p['repository_path']).read_bytes(),'entire frozen source '+n)
    bound=pins['four_bound_source'];need(digest((ROOT/bound['repository_path']).read_bytes())==bound['sha256'],'exact four-bound source')
    need(load('source/four_bounds.json')==json.loads((ROOT/bound['repository_path']).read_text())['bound_steps'],'all four original bounds copied')
    for n,h in pins['independent_helpers'].items():need(digest((ROOT/n).read_bytes())==h,'independent frozen helper '+n)
    foundation_dir=ROOT/pins['foundation994']['directory']
    for n,h in pins['foundation994']['files'].items():need(digest((foundation_dir/n).read_bytes())==h,'sealed994 proof dependency '+n)
    manifest=json.loads((foundation_dir/'MANIFEST.json').read_text())['files']
    need({str(p.relative_to(foundation_dir))for p in foundation_dir.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}==set(manifest),'closed994 file set')
    for n,h in manifest.items():need(digest((foundation_dir/n).read_bytes())==h,'complete994 member '+n)
    build=load('BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'generator pin')
    for n,h in build['sha256'].items():need(digest((HERE/n).read_bytes())==h,'complete generated artifact '+n)
    body=load('source/natural667.json');raw=load('source/raw_builder.json');old=load('source/route_sign.json')
    signed=load('guarded.json');cert=load('domain_certificate.json');bridge=load('BRIDGE994.json')
    b=module('frozen_original_row_bounds',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_mixed994_checker',foundation_dir/'check.py')
    domain_result=domain(body,raw,signed,cert,old,b)
    exact_rows=original_rows(raw,body,load('source/raw_restoration.json'),mixed,b)
    export=raw_export(raw,load('source/gate_ledger.json'),body)
    foundation=json.loads((foundation_dir/'equation.json').read_text())
    bridge_result=bridge994(body,signed,cert,old,foundation,bridge,mixed)
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    results={};mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('corruption accepted '+label)
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='mixed988-independent-')as tmp:
        code=Path(tmp)
        for member,h in pins['read_source_members'].items():
            data=z.read(member);need(digest(data)==h,'exact arithmetic member')
            if Path(member).name!='terminal_elimination.py':(code/Path(member).name).write_bytes(data)
        # No producer/optimizer is imported by this independent checker.
        sys.path.insert(0,str(code));from verify_projection import verify
        inverse=module('frozen_signed_inverse_controls',ROOT/'candidates/projected-radius-integers/check.py')
        for name in NAMES:
            child=load(name+'/equation.json');projection=load(name+'/elimination_certificate.json')
            need(projection['unconstrained_removed']==[],'entire signed parent restored')
            results[name]=dict(restoration=verify(signed,child,projection),
                metrics=full_sos(child,load(name+'/expanded_polynomial.json')),
                arbitrary_signed_restoration_controls=inverse.restoration_controls(signed,child,projection))
            if projection['steps']:
                bad=deepcopy(projection);bad['steps'][0]['restoration'][0][0]+=1
                reject('changed signed inverse '+name,lambda:verify(signed,child,bad))
        bad=deepcopy(cert);bad['bound_steps'][2]['row_combination'][4]['multiplier']=[[-1,[]]]
        reject('changed nonconstant ideal multiplier',lambda:domain(body,raw,signed,bad,old,b))
        bad=deepcopy(cert);bad['bound_steps'][1]['lower']=1
        reject('insufficient n>=1',lambda:domain(body,raw,signed,bad,old,b))
        bad=deepcopy(cert);bad['bound_steps'][2]['lower']=3
        reject('unsupported stronger A>=3',lambda:domain(body,raw,signed,bad,old,b))
        bad=deepcopy(cert);bad['bound_steps'][2],bad['bound_steps'][3]=bad['bound_steps'][3],bad['bound_steps'][2]
        reject('D bound before A',lambda:domain(body,raw,signed,bad,old,b))
        bad=deepcopy(cert);bad['retained_raw_indices'][294]=645
        reject('wrong contracted A identity',lambda:domain(body,raw,signed,bad,old,b))
        bad=deepcopy(cert);bad['seed_indices'].remove(0)
        reject('removed required t0 guard',lambda:domain(body,raw,signed,bad,old,b))
        bad=deepcopy(cert);bad['seed_indices'].remove(326)
        reject('removed required T guard',lambda:domain(body,raw,signed,bad,old,b))
        bad=deepcopy(bridge);bad['shared_guard_transfers'][0]['target_auxiliary'][0]+=1
        reject('wrong literal994 guard slot',lambda:bridge994(body,signed,cert,old,foundation,bad,mixed))
        bad=load('source/raw_restoration.json');bad['omitted'][0]['terms'][0][0]+=1
        reject('changed full raw restoration',lambda:original_rows(raw,body,bad,mixed,b))
        bad=load('support32/expanded_polynomial.json');bad['terms'][0][0]+=1
        reject('changed collected quartic coefficient',lambda:full_sos(load('support32/equation.json'),bad))
        bad=load('support32/equation.json');bad['residuals'].pop()
        reject('missing residual with hash checks bypassed',lambda:verify(signed,bad,load('support32/elimination_certificate.json'),check_hashes=False))
    command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(foundation_dir/'check.py')]
    proc=subprocess.run(command,capture_output=True,text=True);need(proc.returncode==0,'complete frozen994 checker '+proc.stderr)
    foundation_review=json.loads(proc.stdout)
    need(foundation_review['status']=='PASS' and foundation_review['metrics']['variables']==994,
         'actual complete994 domain foundation')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domain=domain_result,
        all_original_row_identities=exact_rows,complete_raw_export=export,literal994_bridge=bridge_result,
        variants=results,rejected_corruptions=mutations,guard_regressions=controls(),
        foundation994=dict(status='PASS',stdout_sha256=digest(proc.stdout.encode())),
        scope='Reverse all integer projections first. Restore592 raw wires over Z, derive A/D signs from four original-row certificates, choose six new guard witnesses, then invoke the frozen994 existential theorem. No pointwise natural restoration, Lean or internal-ZFC claim.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
