#!/usr/bin/env python3
"""Independently verify the whole973 quartic, fifteen-witness bridge and Z maps."""
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
from review_synchronized_certificates import full_sos


def need(ok,text):
    if not ok:raise ValueError(text)


def load(path):return json.loads(path.read_text())
def digest(data):return sha256(data).hexdigest()


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj


def sealed(path):
    files=load(path/'MANIFEST.json')['files']
    need({str(p.relative_to(path))for p in path.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}==set(files),'closed frozen dependency '+str(path))
    for n,h in files.items():need(digest((path/n).read_bytes())==h,'sealed dependency member '+n)


def domain(body,parent,signed,cert,five,b):
    removed=five['removed_guard_identities'];targets={x['contracted_variable']for x in removed}
    need(targets=={29,66,77,91,218},'only five proven sign targets')
    need(cert['removed_guard_identities']==removed,'full actual metadata of omitted guard roles')
    remaining=[g for g in parent['guards']if g['variable']not in targets]
    need(len(remaining)==102 and cert['seed_indices']==[g['variable']for g in remaining],
         'every remaining guard and no extra omission')
    need(signed['domain']=='unrestricted integers'and signed['variables'][:667]==body['variables']
         and signed['residuals'][:585]==body['residuals'],'entire original667/585 body unchanged')
    need(len(signed['variables'])==973 and len(signed['residuals'])==687,'literal973/687 dimensions')
    need(len(cert['guards'])==102,'complete102 guard records')
    for j,old in enumerate(remaining):
        v=old['variable'];a,bb,c=range(667+3*j,670+3*j)
        need(cert['guards'][j]==dict(variable=v,raw_variable=old['raw_variable'],auxiliary=[a,bb,c]),'complete guard identity and slots')
        need(b.poly(signed['residuals'][585+j]['terms'])=={(v,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},
             'entire quadratic guard row')
        need([signed['variables'][i]for i in[a,bb,c]]==[
            dict(kind='nonnegative_guard',name='guard.'+str(v)+'.'+s)for s in['a','b','c']],
            'private guard ownership')
    return dict(body_coordinates=667,body_rows=585,guard_count=102,
        unrestricted_integer_coordinates=973,quadratic_rows=687,omitted_contracted_guard_values=sorted(targets))


def bridge988(parent,cert,five,bridge):
    slots={g['variable']:g['auxiliary']for g in parent['guards']}
    need(bridge['shared_body_coordinates']==667 and bridge['shared_body_rows']==585,'literal common body')
    expected=[dict(variable=g['variable'],raw_variable=g['raw_variable'],source_auxiliary=g['auxiliary'],
        target_auxiliary=slots[g['variable']])for g in cert['guards']]
    fresh=[dict(variable=x['contracted_variable'],raw_variable=x['raw_variable'],
        target_auxiliary=slots[x['contracted_variable']])for x in five['removed_guard_identities']]
    need(bridge['shared_guard_transfers']==expected and len(expected)==102,'all102 literal988 guard transfers')
    need(bridge['new_988_guard_triples']==fresh and len(fresh)==5,'only the five proven values require new witnesses')
    need(sorted(i for x in expected for i in x['source_auxiliary'])==list(range(667,973)),
         'whole source auxiliary partition')
    need(sorted(i for x in expected+fresh for i in x['target_auxiliary'])==list(range(667,988)),
         'whole target auxiliary partition')
    return dict(source_integer_coordinates=973,target_integer_coordinates=988,
        copied_guard_triples=102,new_guard_triples=5,fresh_existential_guard_witnesses=15,
        statement='The exact five raw-row signs supply five Legendre triples into literal988. Reverse by dropping exactly those triples; all667 body values stay fixed.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'frozen input '+n)
    base=ROOT/pins['foundation988'];research=ROOT/pins['five_sign_research'];sealed(base);sealed(research)
    for n,h in load(research/'SOURCE_PINS.json')['files'].items():need(digest((ROOT/n).read_bytes())==h,'five-sign source/helper dependency '+n)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'producer pin')
    for n,h in build['sha256'].items():need(digest((HERE/n).read_bytes())==h,'whole generated artifact '+n)
    body=load(base/'source/natural667.json');raw=load(base/'source/raw_builder.json')
    old=load(base/'domain_certificate.json');parent=load(base/'guarded.json')
    five=load(research/'CERTIFICATE.json');cert=load(HERE/'domain_certificate.json');signed=load(HERE/'guarded.json')
    need(cert['five_sign_certificate_sha256']==digest((research/'CERTIFICATE.json').read_bytes()),'exact five-sign certificate binding')
    b=module('frozen_shifted_sign_polynomials',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_actual_sign_rows',ROOT/'candidates/projected-radius-mixed/check.py')
    signs=module('frozen_five_sign_verifier',research/'check.py')
    sign_result=signs.verify(raw,body,old,five,b,mixed)
    need({g['raw_variable']for g in cert['guards']}==set(five['remaining_raw_guard_indices']),
         'actual102 guarded values are exactly the five-sign hypotheses')
    domain_result=domain(body,old,signed,cert,five,b)
    bridge_result=bridge988(old,cert,five,load(HERE/'BRIDGE988.json'))
    baseline=module('frozen_full988_checker',base/'check.py')
    raw_rows=baseline.original_rows(raw,body,load(base/'source/raw_restoration.json'),mixed,b)
    baseline.domain(body,raw,parent,old,load(base/'source/route_sign.json'),b)
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    results={};mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('corruption accepted '+label)
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='mixed973-independent-')as tmp:
        code=Path(tmp)
        for member,h in pins['read_source_members'].items():
            data=z.read(member);need(digest(data)==h,'exact arithmetic source member')
            if Path(member).name!='terminal_elimination.py':(code/Path(member).name).write_bytes(data)
        # The producer/optimizer is never imported by this checker.
        sys.path.insert(0,str(code));from verify_projection import verify
        controls=module('frozen_arbitrary_Z_inverse_controls',ROOT/'candidates/projected-radius-integers/check.py')
        for name in NAMES:
            child=load(HERE/name/'equation.json');projection=load(HERE/name/'elimination_certificate.json')
            need(projection['unconstrained_removed']==[],'every original integer coordinate restored')
            results[name]=dict(restoration=verify(signed,child,projection),
                metrics=full_sos(child,load(HERE/name/'expanded_polynomial.json')),
                arbitrary_signed_restoration_controls=controls.restoration_controls(signed,child,projection))
            if projection['steps']:
                bad=deepcopy(projection);bad['steps'][0]['restoration'][0][0]+=1
                reject('changed signed inverse '+name,lambda:verify(signed,child,bad))
        bad=deepcopy(cert);bad['seed_indices'].pop()
        reject('extra guard omission',lambda:domain(body,old,signed,bad,five,b))
        bad=load(HERE/'BRIDGE988.json');bad['new_988_guard_triples'][0]['target_auxiliary'][0]+=1
        reject('wrong new literal988 guard slot',lambda:bridge988(old,cert,five,bad))
        bad=load(HERE/'support32/expanded_polynomial.json');bad['terms'][0][0]+=1
        reject('changed full quartic coefficient',lambda:full_sos(load(HERE/'support32/equation.json'),bad))
        bad=load(HERE/'support32/equation.json');bad['residuals'].pop()
        reject('omitted actual residual with hashes bypassed',lambda:verify(signed,bad,load(HERE/'support32/elimination_certificate.json'),check_hashes=False))
    inherited={}
    for name,path in [('five_sign_proof',research/'check.py'),('literal988_foundation',base/'check.py')]:
        command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(path)]
        proc=subprocess.run(command,capture_output=True,text=True)
        need(proc.returncode==0,'complete frozen checker '+name+': '+proc.stderr)
        review=json.loads(proc.stdout);need(review['status']=='PASS','actual checker PASS '+name)
        inherited[name]=dict(status='PASS',stdout_sha256=digest(proc.stdout.encode()))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domain=domain_result,
        all_original_row_identities=raw_rows,five_presemantic_signs=sign_result,literal988_bridge=bridge_result,
        variants=results,rejected_corruptions=mutations,complete_frozen_checks=inherited,
        scope='Every signed projection is reversed first. All592 raw wires are restored over Z; four bounds and975 original-row signs prove the five omitted guard values nonnegative. Fifteen fresh Legendre witnesses yield a literal988 zero. Its unchanged ordinary994/native normalization follows. No pointwise natural, Lean or new internal-ZFC claim.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
