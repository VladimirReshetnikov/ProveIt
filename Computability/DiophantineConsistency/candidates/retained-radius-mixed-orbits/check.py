#!/usr/bin/env python3
"""Independent raw1559/literal967 bijection and all low-height integer quartics."""
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
NAMES=['retained','support2_affine1','support2_affine2','support4_affine2','support8_affine2']
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos
from review_quartics407888 import raw_export


def need(ok,text):
    if not ok:raise ValueError(text)


def load(p):return json.loads(p.read_text())
def digest(d):return sha256(d).hexdigest()


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj


def sealed(path):
    files=load(path/'MANIFEST.json')['files']
    need({str(p.relative_to(path))for p in path.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}==set(files),'closed whole frozen dependency '+str(path))
    for n,h in files.items():need(digest((path/n).read_bytes())==h,'whole frozen dependency member '+n)


def domain(raw,body,target,targetcert,signed,cert,b):
    ids={json.dumps(v,sort_keys=True,separators=(',',':')):i for i,v in enumerate(raw['variables'])}
    need(len(ids)==1259,'all original metadata identities unique')
    retained=[ids[json.dumps(v,sort_keys=True,separators=(',',':'))]for v in body['variables']]
    need(cert['retained_raw_indices']==retained and len(retained)==667,'complete literal retained-body map')
    need(target['variables'][:667]==body['variables']and target['residuals'][:585]==body['residuals'],
         'actual967 target has the exact original body')
    need(signed['domain']=='unrestricted integers'and signed['variables'][:1259]==raw['variables']
         and signed['residuals'][:1177]==[dict(label=r['label'],terms=r['terms'])for r in raw['rows']],
         'all1259 original variables and1177 raw coefficients retained verbatim')
    need(len(signed['variables'])==1559 and len(signed['residuals'])==1277,'literal1559/1277 dimensions')
    need(len(targetcert['guards'])==len(cert['guards'])==100,'all100 unchanged guard roles')
    need(cert['raw_guard_indices']==[g['raw_variable']for g in targetcert['guards']],
         'no guard omission beyond the frozen967 set')
    for j,(g,t)in enumerate(zip(cert['guards'],targetcert['guards'])):
        cv=t['variable'];v=retained[cv];a,bb,c=range(1259+3*j,1262+3*j)
        need(v==t['raw_variable']and g==dict(raw_variable=v,contracted_variable=cv,auxiliary=[a,bb,c]),
             'full metadata/body/guard-position identity')
        need(b.poly(signed['residuals'][1177+j]['terms'])=={(v,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},
             'entire raw guard polynomial')
        need([signed['variables'][i]for i in[a,bb,c]]==[
            dict(kind='nonnegative_guard',name='raw_guard.'+str(v)+'.'+s)for s in['a','b','c']],
            'raw guard auxiliary ownership')
    return dict(raw_body_coordinates=1259,raw_body_rows=1177,integer_coordinates=1559,
        quadratic_rows=1277,guard_count=100,all_original_raw_coefficients_retained=True)


def bridge967(raw,body,target,targetcert,signed,cert,restoration,bridge,mixed,b):
    restored,_=mixed.restoration(raw,body,restoration,set())  # Z identities only; natural subset ignored.
    retained=restoration['retained_raw_indices']
    need(bridge['raw_body_coordinates']==1259 and bridge['raw_body_rows']==1177
         and bridge['target_body_coordinates']==667 and bridge['target_body_rows']==585,
         'literal raw/target body dimensions')
    need(bridge['retained_raw_indices']==retained==cert['retained_raw_indices'],'same complete retained-coordinate map')
    expected=[dict(raw_variable=g['raw_variable'],contracted_variable=g['contracted_variable'],
        source_auxiliary=g['auxiliary'],target_auxiliary=t['auxiliary'])for g,t in zip(cert['guards'],targetcert['guards'])]
    need(bridge['guard_transfers']==expected and len(expected)==100,'all100 actual guard triples copied')
    need(sorted(i for g in expected for i in g['source_auxiliary'])==list(range(1259,1559)),
         'complete raw auxiliary partition')
    need(sorted(i for g in expected for i in g['target_auxiliary'])==list(range(667,967)),
         'complete literal967 auxiliary partition')
    full=dict(restored)
    for g in expected:
        for src,dst in zip(g['source_auxiliary'],g['target_auxiliary']):full[src]={(dst,):1}
    need(len(full)==1559,'all raw and guard inverse recipes defined')
    projection=retained+list(range(1259,1559))
    need(bridge['source_retained_coordinates']==projection and len(set(projection))==967,
         'complete967 forward coordinate selection')
    for i,v in enumerate(projection):need(full[v]=={(i,):1},'restriction after restoration is literal identity')
    rows=bridge['raw_row_to_target_row']
    need(len(rows)==1277 and sorted(i for i in rows if i is not None)==list(range(685))
         and sum(i is None for i in rows)==592,'whole1277-row target partition')
    for rid,(row,tid)in enumerate(zip(signed['residuals'],rows)):
        image={}
        for c,m in row['terms']:
            term={():c}
            for v in m:term=b.mul(term,full[v])
            image=b.add(image,term)
        if tid is None:need(not image,'every deleted raw defining row is identically zero over Z')
        else:
            need(type(tid)is int and 0<=tid<685 and image==b.poly(target['residuals'][tid]['terms']),
                 'every raw/guard row becomes its complete literal967 target row')
            if rid<1177:need(row['label']==target['residuals'][tid]['label'],'original raw row label/target binding')
    return dict(source_integer_coordinates=1559,target_integer_coordinates=967,
        uniquely_restored_affine_body_coordinates=592,copied_guard_triples=100,
        full_original_and_guard_row_identities=1277,zero_defining_row_identities=592,
        nonzero_literal_target_rows=685,restriction_after_restoration_identities=967,
        fresh_existential_witnesses=0,sign_or_semantic_premises_before_target_zero=0,
        statement='Exact Z-zero bijection: restrict retained body values and copy guard witnesses; reverse every triangular monic affine recipe over Z and copy the same witnesses. Invoke frozen967 normalization only after its literal zero exists.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen source '+n)
    base=ROOT/pins['raw_foundation'];target_dir=ROOT/pins['foundation967'];sealed(base);sealed(target_dir)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'generator pin')
    for n,h in build['sha256'].items():need(digest((HERE/n).read_bytes())==h,'complete generated artifact '+n)
    raw=load(base/'source/raw_builder.json');body=load(base/'source/natural667.json')
    target=load(target_dir/'guarded.json');targetcert=load(target_dir/'domain_certificate.json')
    restoration=load(base/'source/raw_restoration.json');signed=load(HERE/'guarded.json');cert=load(HERE/'domain_certificate.json')
    need(cert['literal967_domain_certificate_sha256']==digest((target_dir/'domain_certificate.json').read_bytes()),'whole literal967 guard-set binding')
    bridge=load(HERE/'BRIDGE967.json');need(bridge['affine_restoration_sha256']==digest((base/'source/raw_restoration.json').read_bytes()),'whole592 recipe binding')
    b=module('frozen_integer_polynomial_operations',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen592_affine_recipe_verifier',ROOT/'candidates/projected-radius-mixed/check.py')
    domain_result=domain(raw,body,target,targetcert,signed,cert,b)
    bridge_result=bridge967(raw,body,target,targetcert,signed,cert,restoration,bridge,mixed,b)
    raw_export_result=raw_export(raw,load(base/'source/gate_ledger.json'),body)
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    results={};mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('corruption accepted '+label)
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='raw1559-independent-')as tmp:
        code=Path(tmp)
        for member,h in pins['read_source_members'].items():
            data=z.read(member);need(digest(data)==h,'exact arithmetic verifier member')
            if Path(member).name!='terminal_elimination.py':(code/Path(member).name).write_bytes(data)
        # The producer/optimizer is deliberately never imported here.
        sys.path.insert(0,str(code));from verify_projection import verify
        inverse=module('frozen_off_source_integer_inverse_controls',ROOT/'candidates/projected-radius-integers/check.py')
        for name in NAMES:
            child=load(HERE/name/'equation.json');projection=load(HERE/name/'elimination_certificate.json')
            need(projection['unconstrained_removed']==[],'every parent coordinate uniquely restored')
            results[name]=dict(restoration=verify(signed,child,projection),
                metrics=full_sos(child,load(HERE/name/'expanded_polynomial.json')),
                arbitrary_signed_restoration_controls=inverse.restoration_controls(signed,child,projection))
            if projection['steps']:
                bad=deepcopy(projection);bad['steps'][0]['restoration'][0][0]+=1
                reject('changed signed inverse '+name,lambda:verify(signed,child,bad))
        bad=deepcopy(cert);bad['guards'][0]['raw_variable']+=1
        reject('wrong raw guarded coordinate identity',lambda:domain(raw,body,target,targetcert,signed,bad,b))
        bad=deepcopy(bridge);bad['guard_transfers'][0]['target_auxiliary'][0]+=1
        reject('wrong literal967 witness slot',lambda:bridge967(raw,body,target,targetcert,signed,cert,restoration,bad,mixed,b))
        bad=deepcopy(bridge);i=next(i for i,x in enumerate(bad['raw_row_to_target_row'])if x is None);bad['raw_row_to_target_row'][i]=0
        reject('false augmented raw row partition',lambda:bridge967(raw,body,target,targetcert,signed,cert,restoration,bad,mixed,b))
        bad=deepcopy(restoration);bad['omitted'][0]['terms'][0][0]+=1
        reject('changed592 affine recipe',lambda:bridge967(raw,body,target,targetcert,signed,cert,bad,bridge,mixed,b))
        bad=deepcopy(bridge);bad['source_retained_coordinates'][0]+=1
        reject('wrong forward projection coordinate',lambda:bridge967(raw,body,target,targetcert,signed,cert,restoration,bad,mixed,b))
        bad=load(HERE/'support8_affine2/expanded_polynomial.json');bad['terms'][0][0]+=1
        reject('changed complete low-height coefficient',lambda:full_sos(load(HERE/'support8_affine2/equation.json'),bad))
        bad=load(HERE/'support8_affine2/equation.json');bad['residuals'].pop()
        reject('missing residual with hashes bypassed',lambda:verify(signed,bad,load(HERE/'support8_affine2/elimination_certificate.json'),check_hashes=False))
    command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(target_dir/'check.py')]
    proc=subprocess.run(command,capture_output=True,text=True)
    need(proc.returncode==0,'complete frozen967 checker: '+proc.stderr)
    review=json.loads(proc.stdout);need(review['status']=='PASS'and review['domain']['unrestricted_integer_coordinates']==967,'actual literal967 foundation checked')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domain=domain_result,
        literal967_integer_bijection=bridge_result,complete_raw_export=raw_export_result,
        variants=results,rejected_corruptions=mutations,
        complete_frozen967_check=dict(status='PASS',stdout_sha256=digest(proc.stdout.encode())),
        scope='Every low-height signed projection is reversed over Z, including every guard. The exact592 affine restoration/100-guard witness map gives a literal967 zero with no fresh witnesses or sign assumptions. Only then invoke its private-orbit/973/988/994 ordinary theorem. No pointwise natural or new Lean/internal-ZFC claim.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
