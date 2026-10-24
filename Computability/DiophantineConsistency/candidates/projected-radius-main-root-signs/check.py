#!/usr/bin/env python3
"""Independent full coefficients/Z inverses/domain ledger/literal967 bridge."""
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


def load(p):return json.loads(p.read_text())
def digest(d):return sha256(d).hexdigest()


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj


def sealed(path):
    manifest=path/'MANIFEST.json';files=load(manifest)['files']
    need({str(p.relative_to(path))for p in path.rglob('*')if p.is_file()and p!=manifest}==set(files),'closed whole packet '+str(path))
    for n,h in files.items():need(digest((path/n).read_bytes())==h,'whole sealed member '+n)


def domain(body,old,signed,cert,proof,b):
    remaining=[g for g in old['guards']if g['raw_variable']in proof['remaining_raw_guard_indices']]
    removed=[g for g in old['guards']if g['raw_variable']not in proof['remaining_raw_guard_indices']]
    need(len(remaining)==79 and len(removed)==21 and cert['seed_indices']==[g['variable']for g in remaining],
         'precisely79 actual old guard values retained')
    need(cert['removed_guard_records']==removed==proof['pointwise_map']['missing_target_guard_records'],
         'exact21 omitted X/T guard roles and literal967 slots')
    need({g['raw_variable']for g in remaining}==set(proof['remaining_raw_guard_indices']),'all actual79 guards exactly the sign-theorem hypotheses')
    need(signed['domain']=='unrestricted integers'and signed['variables'][:667]==body['variables']
         and signed['residuals'][:585]==body['residuals'],'every original667/585 coefficient unchanged')
    need(len(signed['variables'])==904 and len(signed['residuals'])==664,'complete904/664 dimensions')
    need(len(cert['guards'])==79,'every private guard recorded')
    for j,g in enumerate(remaining):
        v=g['variable'];a,bb,c=range(667+3*j,670+3*j)
        need(cert['guards'][j]==dict(variable=v,raw_variable=g['raw_variable'],auxiliary=[a,bb,c]),'all actual guard positions')
        need(b.poly(signed['residuals'][585+j]['terms'])=={(v,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},'complete retained guard polynomial')
        need([signed['variables'][i]for i in[a,bb,c]]==[
            dict(kind='nonnegative_guard',name='guard.'+str(v)+'.'+s)for s in['a','b','c']],'guard auxiliary ownership')
    return dict(body_coordinates=667,body_rows=585,guard_count=79,
        unrestricted_integer_coordinates=904,quadratic_rows=664,pointwise_omitted_guard_consequences=21)


def bridge967(body,old,target,signed,cert,proof,bridge,b):
    slots={g['variable']:g['auxiliary']for g in old['guards']}
    expected=[dict(variable=g['variable'],raw_variable=g['raw_variable'],source_auxiliary=g['auxiliary'],
        target_auxiliary=slots[g['variable']])for g in cert['guards']]
    need(bridge['shared_body_coordinates']==667 and bridge['shared_body_rows']==585 and bridge['body_values_changed']==0,
         'whole shared body, with no sign normalization or body change')
    need(bridge['shared_guard_transfers']==expected and len(expected)==79,'all79 literal967 guard transfers')
    missing=proof['pointwise_map']['missing_target_guard_records']
    need(bridge['fresh_967_guard_records']==missing and len(missing)==21,'exact63 new literal967 witness slots')
    need(sorted(i for x in expected for i in x['source_auxiliary'])==list(range(667,904)),'entire source witness partition')
    need(sorted([i for x in expected for i in x['target_auxiliary']]+
                [i for x in missing for i in x['auxiliary']])==list(range(667,967)),'entire literal967 witness partition')
    need(target['variables'][:667]==body['variables']and target['residuals'][:585]==body['residuals'],
         'complete literal967 target body')
    # Expand the target under the explicit extension: old retained witness slots
    # are copied; the21 missing triples become63 new symbolic integer variables.
    mp={i:i for i in range(667)}
    for x in expected:
        for dst,src in zip(x['target_auxiliary'],x['source_auxiliary']):mp[dst]=src
    fresh=[]
    for j,x in enumerate(missing):
        for dst,src in zip(x['auxiliary'],range(904+3*j,907+3*j)):mp[dst]=src
        fresh.append(dict(variable=x['variable'],raw_variable=x['raw_variable'],
            symbolic_new_witnesses=list(range(904+3*j,907+3*j)),literal967_witnesses=x['auxiliary']))
    need(set(mp)==set(range(967))and set(mp.values())==set(range(967)),'whole extension permutation including63 fresh symbols')
    parent_row={g['variable']:585+j for j,g in enumerate(old['guards'])}
    def rename(row):return b.poly([[c,[mp[v]for v in m]]for c,m in row['terms']])
    for j,g in enumerate(cert['guards']):
        need(rename(target['residuals'][parent_row[g['variable']]])==b.poly(signed['residuals'][585+j]['terms']),
             'entire copied target guard row equals actual source row')
    for x in fresh:
        a,bb,c=x['symbolic_new_witnesses'];v=x['variable']
        need(rename(target['residuals'][parent_row[v]])=={(v,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},
             'entire missing target guard row has exactly the proven sign target')
    return dict(source_integer_coordinates=904,target_integer_coordinates=967,
        shared_body_coordinates=667,shared_body_rows=585,copied_guard_triples=79,
        fresh_guard_triples=21,fresh_existential_integer_witnesses=63,
        complete_guard_extension_row_identities=100,body_values_changed=0,
        forward='Restore raw wires over Z, apply the checked pointwise guard-sign theorem, copy79 triples and supply63 fresh Legendre witnesses into literal967.',
        reverse='Forget exactly21 guard triples, retaining identical body values and the79 other triples.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    if(HERE/'MANIFEST.json').exists():sealed(HERE)
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen source '+n)
    target_dir=ROOT/pins['foundation967'];research=ROOT/pins['sign_research'];base=ROOT/pins['raw_foundation']
    for folder in[target_dir,research,base]:sealed(folder)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'producer pin')
    for n,h in build['sha256'].items():need(digest((HERE/n).read_bytes())==h,'whole generated artifact '+n)
    raw=load(base/'source/raw_builder.json');body=load(base/'source/natural667.json');restoration=load(base/'source/raw_restoration.json')
    old=load(target_dir/'domain_certificate.json');target=load(target_dir/'guarded.json');proof=load(research/'CERTIFICATE.json')
    cert=load(HERE/'domain_certificate.json');signed=load(HERE/'guarded.json');bridge=load(HERE/'BRIDGE967.json')
    need(cert['sign_certificate_sha256']==digest((research/'CERTIFICATE.json').read_bytes()),'entire pointwise sign proof binding')
    b=module('frozen_sparse_integer_polynomials',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_all592_integer_restorations',ROOT/'candidates/projected-radius-mixed/check.py')
    baseline=module('frozen_original_raw_body_identities',base/'check.py')
    sign_checker=module('frozen_full_pointwise_sign_checker',research/'check.py')
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json')
    proof_result=sign_checker.verify(raw,body,old,interfaces,proof)
    domain_result=domain(body,old,signed,cert,proof,b);bridge_result=bridge967(body,old,target,signed,cert,proof,bridge,b)
    raw_rows=baseline.original_rows(raw,body,restoration,mixed,b)
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    results={};mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('corruption accepted '+label)
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='mainroot904-independent-')as tmp:
        code=Path(tmp)
        for member,h in pins['read_source_members'].items():
            data=z.read(member);need(digest(data)==h,'exact independent arithmetic member')
            if Path(member).name!='terminal_elimination.py':(code/Path(member).name).write_bytes(data)
        # Producer/optimizer never imported by this checker.
        sys.path.insert(0,str(code));from verify_projection import verify
        inverse=module('frozen_off_source_signed_inverse_controls',ROOT/'candidates/projected-radius-integers/check.py')
        for name in NAMES:
            child=load(HERE/name/'equation.json');projection=load(HERE/name/'elimination_certificate.json')
            need(projection['unconstrained_removed']==[],'all integer parent coordinates restored')
            results[name]=dict(restoration=verify(signed,child,projection),
                metrics=full_sos(child,load(HERE/name/'expanded_polynomial.json')),
                arbitrary_signed_restoration_controls=inverse.restoration_controls(signed,child,projection))
            if projection['steps']:
                bad=deepcopy(projection);bad['steps'][0]['restoration'][0][0]+=1
                reject('changed signed inverse '+name,lambda:verify(signed,child,bad))
        bad=deepcopy(cert);bad['seed_indices'].pop();reject('extra guard omission',lambda:domain(body,old,signed,bad,proof,b))
        bad=deepcopy(cert);bad['removed_guard_records'][0]['raw_variable']+=1;reject('wrong proved sign target',lambda:domain(body,old,signed,bad,proof,b))
        bad=deepcopy(bridge);bad['fresh_967_guard_records'][0]['auxiliary'][0]+=1
        reject('wrong fresh literal967 witness slot',lambda:bridge967(body,old,target,signed,cert,proof,bad,b))
        bad=deepcopy(bridge);bad['shared_guard_transfers'][0]['target_auxiliary'][0]+=1
        reject('wrong copied literal967 witness slot',lambda:bridge967(body,old,target,signed,cert,proof,bad,b))
        bad=deepcopy(bridge);bad['body_values_changed']=1
        reject('nonpointwise map substituted for pointwise extension',lambda:bridge967(body,old,target,signed,cert,proof,bad,b))
        bad=load(HERE/'support32/expanded_polynomial.json');bad['terms'][0][0]+=1
        reject('changed full quartic coefficient',lambda:full_sos(load(HERE/'support32/equation.json'),bad))
        bad=load(HERE/'support32/equation.json');bad['residuals'].pop()
        reject('missing residual with hashes bypassed',lambda:verify(signed,bad,load(HERE/'support32/elimination_certificate.json'),check_hashes=False))
    inherited={}
    for name,path in[('pointwise21_guard_signs',research/'check.py'),('literal967_foundation',target_dir/'check.py')]:
        command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(path)]
        proc=subprocess.run(command,capture_output=True,text=True)
        need(proc.returncode==0,'complete frozen checker '+name+': '+proc.stderr)
        review=json.loads(proc.stdout);need(review['status']=='PASS','actual checker PASS '+name)
        inherited[name]=dict(status='PASS',stdout_sha256=digest(proc.stdout.encode()))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domain=domain_result,
        all_original_row_identities=raw_rows,pointwise_sign_ledger=proof_result,literal967_bridge=bridge_result,
        variants=results,rejected_corruptions=mutations,complete_frozen_checks=inherited,
        scope='Reverse every signed projection first, including guards. Restore592 raw wires over Z and prove the21 omitted guard values nonnegative at that same tuple by the ordered prefix/index/residue proof. Only then choose63 new witnesses into literal967 and invoke its inherited ordinary calibration. Full finite algebra/coefficient/inverse checks; no new Lean or internal-ZFC theorem.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
