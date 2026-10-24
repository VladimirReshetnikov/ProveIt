#!/usr/bin/env python3
"""Full quartic/inverse checks, private orbit domains, literal973 witness map."""
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
    files=load(path/'MANIFEST.json')['files']
    need({str(p.relative_to(path))for p in path.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}==set(files),'closed frozen dependency '+str(path))
    for n,h in files.items():need(digest((path/n).read_bytes())==h,'whole sealed dependency member '+n)


def substitute(p,mapping,b):
    out={}
    for m,c in p.items():
        term={():c}
        for v in m:term=b.mul(term,mapping.get(v,{(v,):1}))
        out=b.add(out,term)
    return out


def evaluate(terms,values):
    total=0
    for c,m in terms:
        for i in m:c*=values[i]
        total+=c
    return total


def domain(body,old,signed,cert,orbit,b):
    targets={295,301};remaining=[g for g in old['guards']if g['variable']not in targets]
    need(len(remaining)==100 and cert['seed_indices']==[g['variable']for g in remaining],
         'precisely100 old guard values retained')
    need(cert['removed_guard_triples']==orbit['new_973_guard_triples']and
         {(g['variable'],g['raw_variable'])for g in cert['removed_guard_triples']}=={(295,645),(301,655)},
         'actual private Zminus1/U guard identities')
    need({g['raw_variable']for g in remaining}==set(orbit['remaining_raw_guard_indices']),
         'the actual100 guards are exactly the orbit hypotheses')
    need(signed['domain']=='unrestricted integers'and signed['variables'][:667]==body['variables']
         and signed['residuals'][:585]==body['residuals'],'every original667/585 coefficient unchanged')
    need(len(signed['variables'])==967 and len(signed['residuals'])==685,'complete967/685 dimensions')
    need(len(cert['guards'])==100,'every private guard recorded')
    for j,g in enumerate(remaining):
        v=g['variable'];a,bb,c=range(667+3*j,670+3*j)
        need(cert['guards'][j]==dict(variable=v,raw_variable=g['raw_variable'],auxiliary=[a,bb,c]),'all actual guard coordinate positions')
        need(b.poly(signed['residuals'][585+j]['terms'])=={(v,):1,(a,a):-1,(bb,bb):-1,(c,):-1,(c,c):-1},'entire private guard polynomial')
        need([signed['variables'][i]for i in[a,bb,c]]==[
            dict(kind='nonnegative_guard',name='guard.'+str(v)+'.'+s)for s in['a','b','c']],
            'private guard ownership')
    whole_symmetries=[]
    for o in orbit['orbits']:
        mp={item['variable']:b.poly(item['terms'])for item in o['contracted_affine_map']}
        signs=o['contracted_row_signs']+[1]*100
        for row,sign in zip(signed['residuals'],signs):
            p=b.poly(row['terms']);need(substitute(p,mp,b)=={m:sign*c for m,c in p.items()},
                 'every complete967 residual is invariant up to sign')
        for v in cert['seed_indices']:need(mp.get(v,{(v,):1})=={(v,):1},'every retained guarded body value fixed')
        whole_symmetries.append(dict(name=o['name'],full_integer_rows=685,
            fixed_guard_values=100,negated_rows=[i for i,s in enumerate(signs)if s==-1]))
    return dict(body_coordinates=667,body_rows=585,guard_count=100,unrestricted_integer_coordinates=967,
        quadratic_rows=685,complete_integer_row_symmetries=whole_symmetries)


def bridge973(old,cert,orbit,bridge):
    slots={g['variable']:g['auxiliary']for g in old['guards']}
    expected=[dict(variable=g['variable'],raw_variable=g['raw_variable'],source_auxiliary=g['auxiliary'],
        target_auxiliary=slots[g['variable']])for g in cert['guards']]
    need(bridge['shared_body_coordinates']==667 and bridge['shared_body_rows']==585,'whole shared body dimensions')
    need(bridge['shared_guard_transfers']==expected and len(expected)==100,'all100 literal973 guard transfers')
    need(bridge['new_973_guard_triples']==orbit['new_973_guard_triples'],'exact six new literal973 guard slots')
    need(sorted(i for x in expected for i in x['source_auxiliary'])==list(range(667,967)),'entire source auxiliary partition')
    need(sorted([i for x in expected for i in x['target_auxiliary']]+
                [i for x in bridge['new_973_guard_triples']for i in x['auxiliary']])==list(range(667,973)),
         'entire target auxiliary partition')
    normalized=[dict(name=o['name'],target_contracted_variable=o['target_contracted_variable'],
        contracted_affine_map=o['contracted_affine_map'],
        branch='apply iff U<0; U=0 uses identity'if o['name']=='U'else'apply iff Zminus1<=-2; -1 is excluded independently by A>=2')for o in orbit['orbits']]
    need(bridge['normalization']==normalized,'exact two branch-dependent maps, including U zero branch')
    return dict(source_integer_coordinates=967,target_integer_coordinates=973,copied_guard_triples=100,
        fresh_guard_triples=2,fresh_existential_integer_witnesses=6,
        forward='Normalize private body coordinates first, fixing all100 old guarded values and all643 semantic-prefix values; copy their guard witnesses, then choose two Legendre triples.',
        reverse='Forget precisely the two private guard triples; no inverse normalization is claimed.')


def branch_controls(signed,cert,orbit):
    cases=zero_u=0
    for u in[-7,0,7]:
        for z in[-8,-2,0,6]:
            values=[((i+3)*7)%9-4 for i in range(967)]
            for v in cert['seed_indices']:values[v]=v%5
            values[301]=u;values[295]=z;before=list(values);signs=[1]*685
            for o,apply in zip(orbit['orbits'],[u<0,z<=-2]):
                if not apply:continue
                previous=list(values)
                for item in o['contracted_affine_map']:values[item['variable']]=evaluate(item['terms'],previous)
                signs=[a*b for a,b in zip(signs,o['contracted_row_signs']+[1]*100)]
            need(values[301]>=0 and values[295]>=0,'both normalized guard domains')
            need(all(values[v]==before[v]for v in cert['seed_indices']),'all100 guarded values fixed in branch control')
            for row,sign in zip(signed['residuals'],signs):
                need(evaluate(row['terms'],values)==sign*evaluate(row['terms'],before),'whole row branch diagnostic')
            if u==0:
                need(values[301]==0,'U=0 branch is allowed and remains identity');zero_u+=1
            cases+=1
    return dict(arbitrary_signed_full_row_cases=cases,U_zero_identity_cases=zero_u,
        Zminus1_minus_one='excluded universally by the exact norm ideal and A>=2, not tested away')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'entire frozen source '+n)
    parent_dir=ROOT/pins['foundation973'];research=ROOT/pins['orbit_research'];base=ROOT/pins['raw_foundation']
    for folder in[parent_dir,research,base]:sealed(folder)
    for n,h in load(research/'SOURCE_PINS.json')['files'].items():need(digest((ROOT/n).read_bytes())==h,'orbit helper/source dependency '+n)
    build=load(HERE/'BUILD.json');need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'producer pin')
    for n,h in build['sha256'].items():need(digest((HERE/n).read_bytes())==h,'entire generated artifact '+n)
    raw=load(base/'source/raw_builder.json');body=load(base/'source/natural667.json')
    restoration=load(base/'source/raw_restoration.json');old=load(parent_dir/'domain_certificate.json')
    orbit=load(research/'CERTIFICATE.json');cert=load(HERE/'domain_certificate.json');signed=load(HERE/'guarded.json')
    need(cert['orbit_certificate_sha256']==digest((research/'CERTIFICATE.json').read_bytes()),'whole orbit proof binding')
    b=module('frozen_shifted_positive_polynomials',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_raw_integer_restoration',ROOT/'candidates/projected-radius-mixed/check.py')
    baseline=module('frozen_original_t_T_bounds',base/'check.py')
    orbit_checker=module('frozen_complete_orbit_verifier',research/'check.py')
    orbit_result=orbit_checker.verify(raw,body,restoration,old,orbit,b,mixed,baseline)
    domain_result=domain(body,old,signed,cert,orbit,b)
    bridge_result=bridge973(old,cert,orbit,load(HERE/'BRIDGE973.json'))
    raw_rows=baseline.original_rows(raw,body,restoration,mixed,b)
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    results={};mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('corruption accepted '+label)
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='mixed967-independent-')as tmp:
        code=Path(tmp)
        for member,h in pins['read_source_members'].items():
            data=z.read(member);need(digest(data)==h,'exact independent arithmetic member')
            if Path(member).name!='terminal_elimination.py':(code/Path(member).name).write_bytes(data)
        # The producer and optimizer are never imported in the checker.
        sys.path.insert(0,str(code));from verify_projection import verify
        inverse=module('frozen_signed_inverse_diagnostics',ROOT/'candidates/projected-radius-integers/check.py')
        for name in NAMES:
            child=load(HERE/name/'equation.json');projection=load(HERE/name/'elimination_certificate.json')
            need(projection['unconstrained_removed']==[],'entire integer parent restored')
            results[name]=dict(restoration=verify(signed,child,projection),
                metrics=full_sos(child,load(HERE/name/'expanded_polynomial.json')),
                arbitrary_signed_restoration_controls=inverse.restoration_controls(signed,child,projection))
            if projection['steps']:
                bad=deepcopy(projection);bad['steps'][0]['restoration'][0][0]+=1
                reject('changed signed inverse '+name,lambda:verify(signed,child,bad))
        bad=deepcopy(cert);bad['seed_indices'].pop()
        reject('extra guard omission',lambda:domain(body,old,signed,bad,orbit,b))
        bad=load(HERE/'BRIDGE973.json');bad['new_973_guard_triples'][0]['auxiliary'][0]+=1
        reject('wrong new literal973 guard slot',lambda:bridge973(old,cert,orbit,bad))
        bad=load(HERE/'BRIDGE973.json');bad['normalization'][0]['branch']='apply iff U<=0'
        reject('changed specified U-zero branch',lambda:bridge973(old,cert,orbit,bad))
        bad=load(HERE/'support32/expanded_polynomial.json');bad['terms'][0][0]+=1
        reject('changed entire quartic coefficient',lambda:full_sos(load(HERE/'support32/equation.json'),bad))
        bad=load(HERE/'support32/equation.json');bad['residuals'].pop()
        reject('missing actual residual with hashes bypassed',lambda:verify(signed,bad,load(HERE/'support32/elimination_certificate.json'),check_hashes=False))
    inherited={}
    for name,path in[('complete_private_orbits',research/'check.py'),('literal973_foundation',parent_dir/'check.py')]:
        command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(path)]
        proc=subprocess.run(command,capture_output=True,text=True)
        need(proc.returncode==0,'frozen checker '+name+': '+proc.stderr)
        review=json.loads(proc.stdout);need(review['status']=='PASS','actual checker PASS '+name)
        inherited[name]=dict(status='PASS',stdout_sha256=digest(proc.stdout.encode()))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domain=domain_result,
        all_original_row_identities=raw_rows,complete_orbit_normalization=orbit_result,literal973_bridge=bridge_result,
        branch_regressions=branch_controls(signed,cert,orbit),variants=results,rejected_corruptions=mutations,
        complete_frozen_checks=inherited,
        scope='Reverse every signed projection first; restore raw wires and derive A>=2 from retained t0/T. Normalize private U/Z domains by certified affine involutions, fixing all100 guard values and643 semantic-prefix values. Only then supply six Legendre witnesses into literal973. No pointwise natural, new Lean or internal-ZFC claim.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
