#!/usr/bin/env python3
"""Independent full coefficients/Z inverses and nonpointwise literal904 bridge."""
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


def domain(body,old,signed,cert,b):
    remaining=[g for g in old['guards']if g['raw_variable']!=657]
    missing=[g for g in old['guards']if g['raw_variable']==657]
    need(len(remaining)==78 and missing==[dict(variable=303,raw_variable=657,auxiliary=[850,851,852])],'literal q4 guard boundary')
    need(cert['seed_indices']==[g['variable']for g in remaining]and cert['removed_q4_guard_record']==missing[0],'exact78 retained guards; only q4 removed')
    need(signed['domain']=='unrestricted integers'and signed['variables'][:667]==body['variables']and signed['residuals'][:585]==body['residuals'],'entire original667/585 body unchanged')
    need(len(signed['variables'])==901 and len(signed['residuals'])==663 and len(cert['guards'])==78,'complete901/663 source')
    for j,g in enumerate(remaining):
        v=g['variable'];a,bb,c=range(667+3*j,670+3*j)
        need(cert['guards'][j]==dict(variable=v,raw_variable=g['raw_variable'],auxiliary=[a,bb,c]),'all actual78 guard identities/positions')
        need(b.poly(signed['residuals'][585+j]['terms'])=={(v,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},'whole retained guard residual')
        need([signed['variables'][i]for i in[a,bb,c]]==[dict(kind='nonnegative_guard',name='guard.'+str(v)+'.'+s)for s in['a','b','c']],'guard witness ownership')
    return dict(body_coordinates=667,body_rows=585,guard_count=78,unrestricted_integer_coordinates=901,quadratic_rows=663,
        omitted_q4_value_not_pointwise_nonnegative=True)


def bridge904(raw,body,old,target,signed,cert,bridge,interfaces,closure,b):
    slots={g['variable']:g['auxiliary']for g in old['guards']}
    expected=[dict(variable=g['variable'],raw_variable=g['raw_variable'],source_auxiliary=g['auxiliary'],target_auxiliary=slots[g['variable']])for g in cert['guards']]
    need(bridge['shared_body_coordinates']==667 and bridge['shared_body_rows']==585 and bridge['shared_guard_transfers']==expected,'all78 fixed-value target904 witness transfers')
    need(bridge['fresh_q4_guard_record']==dict(variable=303,raw_variable=657,auxiliary=[850,851,852]),'fresh target904 q4 guard slots')
    need(sorted(i for g in expected for i in g['source_auxiliary'])==list(range(667,901))and
         sorted([i for g in expected for i in g['target_auxiliary']]+[850,851,852])==list(range(667,904)),'complete source/target witness partitions')
    need(bridge['all_free_recipes_read_original_tuple']is True and bridge['original_q4_need_not_be_nonnegative']is True and bridge['retained_guard_values_fixed']==78,
         'explicit snapshot/nonpointwise semantics, never original-q4 positivity')
    def rawref(v):return['raw',v]
    def I(c):return['integer',c]
    def E(name,*xs):return[name,*xs]
    t=E('add',E('abs',rawref(657)),I(1));absU=E('abs',rawref(655))
    Bnew=E('add',rawref(667),E('mul',I(4),rawref(656),absU,t))
    recipes=[dict(raw_variable=657,expression=E('add',rawref(657),E('mul',absU,t))),
        dict(raw_variable=658,expression=E('add',rawref(658),E('mul',I(4),rawref(656),E('sign',rawref(655)),t)))]
    for s in interfaces['seeds']:
        k=s['exponent'][1];Sn=E('pellChi',Bnew,rawref(k));Rn=E('pellPsi',Bnew,rawref(k))
        exprs={'S':Sn,'R':Rn,'Squotient':E('exactQuotient',E('sub',Sn,rawref(s['X'][1])),rawref(655)),
            'Rquotient':E('exactQuotient',E('sub',Rn,rawref(k)),E('mul',I(4),rawref(s['Y'][1])))}
        for key in['S','R','Squotient','Rquotient']:recipes.append(dict(raw_variable=s[key][1],expression=exprs[key]))
    need(bridge['free_witness_recipes']==recipes and len(recipes)==62,'all62 literal ordinary witness recipes, with exact divisibility obligations')
    boundary=dict(changed_free_coordinates=closure['changed_free_coordinates'],changed_gate_rows=closure['affected_gate_rows'],affected_constraints=closure['affected_nongate_rows'])
    need(bridge['raw_lift_boundary']==boundary,'entire independent62/141/46 actual raw-use ledger')
    changed=set(boundary['changed_free_coordinates'])|{g['variable']for g in boundary['changed_gate_rows']}
    need({g['raw_variable']for g in cert['guards']}==set(closure['unchanged_guard_indices'])and not changed&set(closure['unchanged_guard_indices']),
         'all78 actual guard values fixed under the full lift')
    need(target['variables'][:667]==body['variables']and target['residuals'][:585]==body['residuals'],'literal904 target uses exact raw-to667 body')
    mp={i:i for i in range(667)}
    for g in expected:
        for dst,src in zip(g['target_auxiliary'],g['source_auxiliary']):mp[dst]=src
    rows={g['variable']:585+j for j,g in enumerate(old['guards'])}
    for j,g in enumerate(cert['guards']):
        image=b.poly([[c,[mp[v]for v in m]]for c,m in target['residuals'][rows[g['variable']]]['terms']])
        need(image==b.poly(signed['residuals'][585+j]['terms']),'every copied904 guard row equals actual source at its fixed guard value')
    a,bb,c=[850,851,852]
    need(b.poly(target['residuals'][rows[303]]['terms'])=={(303,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},'fresh target residual guards the new303/raw657 value')
    return dict(source_integer_coordinates=901,target_integer_coordinates=904,copied_guard_triples=78,fresh_integer_witnesses=3,
        changed_free_raw_coordinates=62,reevaluated_raw_gates=141,restored_raw_nongate_constraints=46,
        complete_fixed_guard_row_identities=78,original_q4_nonnegative_claim=False,
        order='Reverse projections; restore592 raw wires over Z; signed-B index/residue orientation; existingU/V comparison lift; copy78 fixed-value triples; three fresh witnesses for NEW q4; literal904; its pointwise21-sign theorem to967.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    if(HERE/'MANIFEST.json').exists():sealed(HERE)
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen source '+n)
    target_dir=ROOT/pins['foundation904'];research=ROOT/pins['sign_research'];base=ROOT/pins['raw_foundation']
    lift_dir=ROOT/pins['base_lift_research']
    for folder in[target_dir,research,base,lift_dir]:sealed(folder)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'producer pin')
    for n,h in build['sha256'].items():need(digest((HERE/n).read_bytes())==h,'whole generated artifact '+n)
    raw=load(base/'source/raw_builder.json');body=load(base/'source/natural667.json');restoration=load(base/'source/raw_restoration.json')
    old=load(target_dir/'domain_certificate.json');target=load(target_dir/'guarded.json');proof=load(research/'CERTIFICATE.json')
    cert=load(HERE/'domain_certificate.json');signed=load(HERE/'guarded.json');bridge=load(HERE/'BRIDGE904.json')
    need(cert['lift_proof_sha256']==digest((lift_dir/'README.md').read_bytes())and cert['lift_audit_sha256']==digest((lift_dir/'VERIFY.json').read_bytes()),'whole comparison-base proof/audit binding')
    b=module('frozen_sparse_integer_polynomials',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_all592_integer_restorations',ROOT/'candidates/projected-radius-mixed/check.py')
    baseline=module('frozen_original_raw_body_identities',base/'check.py')
    lift_peer=module('frozen_independent_full_signed_B_lift_peer',ROOT/pins['base_lift_peer'])
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json')
    proof_result=lift_peer.literal_audit(raw,interfaces,proof)
    domain_result=domain(body,old,signed,cert,b);bridge_result=bridge904(raw,body,old,target,signed,cert,bridge,interfaces,proof_result,b)
    raw_rows=baseline.original_rows(raw,body,restoration,mixed,b)
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    results={};mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('corruption accepted '+label)
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='comparison901-independent-')as tmp:
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
        bad=deepcopy(cert);bad['seed_indices'].pop();reject('extra guard omission',lambda:domain(body,old,signed,bad,b))
        bad=deepcopy(cert);bad['removed_q4_guard_record']['raw_variable']+=1;reject('wrong omitted q4 identity',lambda:domain(body,old,signed,bad,b))
        bad=deepcopy(bridge);bad['fresh_q4_guard_record']['auxiliary'][0]+=1
        reject('wrong new-q4 literal904 witness slot',lambda:bridge904(raw,body,old,target,signed,cert,bad,interfaces,proof_result,b))
        bad=deepcopy(bridge);bad['shared_guard_transfers'][0]['target_auxiliary'][0]+=1
        reject('wrong copied literal904 witness slot',lambda:bridge904(raw,body,old,target,signed,cert,bad,interfaces,proof_result,b))
        bad=deepcopy(bridge);bad['original_q4_need_not_be_nonnegative']=False
        reject('pointwise old-q4 positivity substituted for lift',lambda:bridge904(raw,body,old,target,signed,cert,bad,interfaces,proof_result,b))
        bad=deepcopy(bridge);bad['free_witness_recipes'][0]['expression'][2][0]='sub'
        reject('changed fixed-unit q4 lift',lambda:bridge904(raw,body,old,target,signed,cert,bad,interfaces,proof_result,b))
        bad=deepcopy(bridge);bad['raw_lift_boundary']['affected_constraints'].pop()
        reject('missing affected comparison constraint',lambda:bridge904(raw,body,old,target,signed,cert,bad,interfaces,proof_result,b))
        bad=load(HERE/'support32/expanded_polynomial.json');bad['terms'][0][0]+=1
        reject('changed full quartic coefficient',lambda:full_sos(load(HERE/'support32/equation.json'),bad))
        bad=load(HERE/'support32/equation.json');bad['residuals'].pop()
        reject('missing residual with hashes bypassed',lambda:verify(signed,bad,load(HERE/'support32/elimination_certificate.json'),check_hashes=False))
    inherited={}
    commands=[('signed_B_author_audit',[str(lift_dir/'audit.py'),'--output','TEMP']),
        ('signed_B_independent_peer',[str(ROOT/pins['base_lift_peer']),'--output','TEMP']),
        ('literal904_foundation',[str(target_dir/'check.py')])]
    with tempfile.TemporaryDirectory(prefix='comparison901-inherited-')as tmp:
        for name,tail in commands:
            command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(Path(tmp)/(name+'.json'))if x=='TEMP'else x for x in tail]
            proc=subprocess.run(command,capture_output=True,text=True)
            need(proc.returncode==0,'complete frozen checker '+name+': '+proc.stderr)
            review=json.loads(proc.stdout);need(review['status']=='PASS','actual checker PASS '+name)
            inherited[name]=dict(status='PASS',stdout_sha256=digest(proc.stdout.encode()))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domain=domain_result,
        all_original_row_identities=raw_rows,complete_nonpointwise_lift_ledger=proof_result,literal904_nonpointwise_bridge=bridge_result,
        variants=results,rejected_corruptions=mutations,complete_frozen_checks=inherited,
        scope='Reverse signed projections and restore592 raw wires over Z. Use signed-B index/residue orientation, then the existingU/V nonpointwise comparison lift fixing78 guarded values; add3 fresh witnesses for NEW q4 into literal904. Its pointwise21-sign theorem then reaches967. Full coefficients/inverses/use ledger; no original-q4 positivity, new Lean or internal-ZFC theorem.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
