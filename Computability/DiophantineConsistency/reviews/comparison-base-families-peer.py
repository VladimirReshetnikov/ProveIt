#!/usr/bin/env python3
"""Independent integer inverse/guard/snapshot bridge peer for the78-guard family.

Imports only our earlier independent polynomial collector, never an author
builder/checker/optimizer or an archived emitter.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('independent_poly',ROOT/'reviews/main-root-modulus-signs-peer.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
P,C,V,add,mul=p.P,p.C,p.V,p.plus,p.times

def need(ok,message):
    if not ok:raise ValueError(message)

def load(path):return json.loads(path.read_bytes())
def sha(path):return sha256(path.read_bytes()).hexdigest()

def sealed(folder):
    manifest=folder/'MANIFEST.json'
    if not manifest.exists():return {'sealed':False}
    files=load(manifest)['files']
    need({str(f.relative_to(folder))for f in folder.rglob('*')if f.is_file()and f!=manifest}==set(files),'closed candidate file inventory')
    for relative,h in files.items():need(sha(folder/relative)==h,'closed candidate member '+relative)
    return {'sealed':True,'manifest_sha256':sha(manifest),'files':len(files)+1}

def substitute(polynomial,variable,replacement):
    out={}
    for monomial,coefficient in polynomial.items():
        term=C(coefficient)
        for v in monomial:term=mul(term,replacement if v==variable else V(v))
        out=add(out,term)
    return out

def projection(parent,child,certificate):
    need(parent['domain']==child['domain']=='unrestricted integers','integer domains')
    need(certificate['unconstrained_removed']==[],'no coordinate forgotten without an inverse')
    rows={i:P(row['terms'])for i,row in enumerate(parent['residuals'])}
    active=set(range(len(parent['variables'])))
    pivots=[]
    for step in certificate['steps']:
        v,r=step['variable'],step['row_id']
        need(v in active and r in rows,'fresh active inverse pivot')
        row=rows[r];coefficient=row.get((v,))
        need(coefficient in(-1,1)and all(v not in m or m==(v,)for m in row),'complete signed unit pivot')
        replacement={m:-coefficient*c for m,c in row.items()if m!=(v,)}
        need(replacement==P(step['restoration'])and p.vars_(replacement)<=active-{v},'whole inverse over earlier active integer coordinates')
        need(parent['variables'][v]['kind']==step['kind']and parent['variables'][v]['name']==step['name'],'literal pivot ownership')
        del rows[r];active.remove(v);pivots.append((v,r))
        rows={i:substitute(q,v,replacement)if v in p.vars_(q)else q for i,q in rows.items()}
    retained=certificate['retained_original_variables'];retained_rows=certificate['retained_original_rows']
    need(retained==sorted(active)and retained_rows==sorted(rows),'complete active parent coordinate and row inventories')
    need([parent['variables'][v]for v in retained]==child['variables'],'all retained child metadata')
    renumber={v:i for i,v in enumerate(retained)}
    need(len(child['residuals'])==len(retained_rows),'complete child residual list')
    for original,row in zip(retained_rows,child['residuals']):
        expected=P([[c,[renumber[v]for v in m]]for m,c in rows[original].items()])
        need(expected==P(row['terms'])and parent['residuals'][original]['label']==row['label'],'every child residual coefficient after every signed substitution')
    return {'signed_unit_steps':len(pivots),'all_guard_rows_in_parent_before_inverse':True,
            'parent_variables':len(parent['variables']),'child_variables':len(child['variables']),
            'parent_rows':len(parent['residuals']),'child_rows':len(child['residuals'])}

def raw_restore(raw,body,certificate):
    retained=certificate['retained_raw_indices']
    need(retained==sorted(set(retained))and len(retained)==667,'whole retained raw coordinate inventory')
    need([raw['variables'][v]for v in retained]==body['variables'],'actual raw/body metadata correspondence')
    restored={v:V(i)for i,v in enumerate(retained)}
    original_gate_rows={row['gate']:P(row['terms'])for row in raw['rows']if row.get('gate')is not None}
    omitted=certificate['omitted']
    need([x['raw_variable']for x in omitted]==sorted(set(range(1259))-set(retained)),'all592 omitted raw coordinates have recipes')
    for item in omitted:
        v=item['raw_variable'];row=original_gate_rows[v]
        need(row.get((v,))==1 and all(v not in m or m==(v,)for m in row),'unique monic raw affine pivot')
        expected={}
        for monomial,coefficient in row.items():
            if monomial==(v,):continue
            need(len(monomial)<=1 and all(i<v for i in monomial),'triangular raw affine reconstruction')
            term=C(-coefficient)
            for i in monomial:term=mul(term,restored[i])
            expected=add(expected,term)
        need(expected==P(item['terms']),'every complete raw restoring polynomial')
        restored[v]=expected
    images=[];zeros=0
    for row in raw['rows']:
        image={}
        for coefficient,monomial in row['terms']:
            term=C(coefficient)
            for v in monomial:term=mul(term,restored[v])
            image=add(image,term)
        if image:images.append((row['label'],image))
        else:zeros+=1
    need(images==[(row['label'],P(row['terms']))for row in body['residuals']]and zeros==592,'every1177 original row becomes exact body row or zero')
    return restored,{'restored_coordinates':len(omitted),'original_rows':len(raw['rows']),
                     'body_rows':len(images),'zero_definition_rows':zeros}

def compact(folder,bridge_override=None,domain_override=None):
    pins=load(folder/'SOURCE_PINS.json')
    for relative,h in pins['files'].items():need(sha(ROOT/relative)==h,'whole frozen source '+relative)
    base=ROOT/pins['raw_foundation'];foundation=ROOT/pins['foundation904']
    raw=load(base/'source/raw_builder.json');body=load(base/'source/natural667.json')
    restored,restoration=raw_restore(raw,body,load(base/'source/raw_restoration.json'))
    signed=load(folder/'guarded.json');domain=load(folder/'domain_certificate.json')if domain_override is None else domain_override
    target=load(foundation/'guarded.json');old=load(foundation/'domain_certificate.json')
    bridge=load(folder/'BRIDGE904.json')if bridge_override is None else bridge_override
    oldguards=old['guards'];guards=[g for g in oldguards if g['raw_variable']!=657]
    need(len(guards)==78 and len(signed['variables'])==901 and len(signed['residuals'])==663,'whole901/78guard parent')
    need(signed['domain']=='unrestricted integers'and signed['variables'][:667]==body['variables']and signed['residuals'][:585]==body['residuals'],'entire unchanged integer body before lift')
    need(domain['seed_indices']==[g['variable']for g in guards],'exact retained guard identities')
    transfers=[]
    for j,g in enumerate(guards):
        v=g['variable'];aux=list(range(667+3*j,670+3*j))
        need(domain['guards'][j]==dict(variable=v,raw_variable=g['raw_variable'],auxiliary=aux),'complete source guard record')
        need(restored[g['raw_variable']]==V(v),'guard actual raw value is exactly its compact body coordinate')
        a,b,c=aux
        need(P(signed['residuals'][585+j]['terms'])=={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'whole source Legendre guard row')
        transfers.append(dict(variable=v,raw_variable=g['raw_variable'],source_auxiliary=aux,target_auxiliary=g['auxiliary']))
    need(bridge['shared_guard_transfers']==transfers,'all78 exact fixed-value simultaneous witness transfers')
    need(bridge['fresh_q4_guard_record']==dict(variable=303,raw_variable=657,auxiliary=[850,851,852]),'fresh guard is for NEWq4 at the exact literal904 slots')
    need(bridge['all_free_recipes_read_original_tuple']is True and bridge['original_q4_need_not_be_nonnegative']is True,'explicit snapshot and existential semantics')
    need(restored[657]==V(303),'actual q4 raw/compact identity')
    need(target['variables'][:667]==body['variables']and target['residuals'][:585]==body['residuals'],'literal904 target has the same body equations, not assumed same tuple')
    oldrows={g['variable']:585+j for j,g in enumerate(oldguards)}
    for g in transfers:
        v=g['variable'];a,b,c=g['target_auxiliary']
        need(P(target['residuals'][oldrows[v]]['terms'])=={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'entire fixed-value target guard residual')
    need(sorted(i for g in transfers for i in g['source_auxiliary'])==list(range(667,901))and
         sorted([i for g in transfers for i in g['target_auxiliary']]+[850,851,852])==list(range(667,904)),
         'complete disjoint source/target witness partitions; no copied oldq4 triple')
    closure=load(ROOT/'research/comparison-base-sign/VERIFY.json')
    expected_boundary={k:closure[v]for k,v in [('changed_free_coordinates','changed_free_coordinates'),('changed_gate_rows','changed_gate_rows'),('affected_constraints','affected_private_constraints')]}
    need(bridge['raw_lift_boundary']==expected_boundary,'fresh independent62/141/46 closure, not a metadata-only privacy premise')
    changed=set(expected_boundary['changed_free_coordinates'])|{g['variable']for g in expected_boundary['changed_gate_rows']}
    need(not changed&{g['raw_variable']for g in guards},'all78 copied guards have literally fixed raw values')
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json')
    ref=lambda v:['raw',v]
    I=lambda v:['integer',v]
    E=lambda op,*args:[op,*args]
    t=E('add',E('abs',ref(657)),I(1))
    Bnew=E('add',ref(667),E('mul',I(4),ref(656),E('abs',ref(655)),t))
    recipes=[dict(raw_variable=657,expression=E('add',ref(657),E('mul',E('abs',ref(655)),t))),
             dict(raw_variable=658,expression=E('add',ref(658),E('mul',I(4),ref(656),E('sign',ref(655)),t)))]
    for seed in interfaces['seeds']:
        k=seed['exponent'][1];s=E('pellChi',Bnew,ref(k));r=E('pellPsi',Bnew,ref(k))
        formulas={'S':s,'R':r,'Squotient':E('exactQuotient',E('sub',s,ref(seed['X'][1])),ref(655)),
                  'Rquotient':E('exactQuotient',E('sub',r,ref(k)),E('mul',I(4),ref(seed['Y'][1])))}
        for key in ('S','R','Squotient','Rquotient'):recipes.append(dict(raw_variable=seed[key][1],expression=formulas[key]))
    need(bridge['free_witness_recipes']==recipes and len(recipes)==62,'all62 exact original-snapshot free witness recipes')
    variants={}
    for name in ['unprojected','support4','support8','support16','support32']:
        variants[name]=projection(signed,load(folder/name/'equation.json'),load(folder/name/'elimination_certificate.json'))
    return {'raw_integer_restoration':restoration,'source_guards':78,'snapshot_free_recipes':len(recipes),
            'fixed_guard_transfers':len(transfers),'fresh_new_q4_witnesses':3,
            'original_q4_naturality_not_assumed':True,'signed_projection_inverses':variants}

def retained(folder,bridge_override=None,lift_override=None):
    pins=load(folder/'SOURCE_PINS.json')
    for relative,h in pins['files'].items():need(sha(ROOT/relative)==h,'whole raw-family frozen source '+relative)
    base=ROOT/pins['raw_foundation'];foundation=ROOT/pins['foundation901']
    raw=load(base/'source/raw_builder.json');body=load(base/'source/natural667.json')
    rc=load(base/'source/raw_restoration.json');restored,restoration=raw_restore(raw,body,rc)
    signed=load(folder/'guarded.json');domain=load(folder/'domain_certificate.json')
    target=load(foundation/'guarded.json');targetdomain=load(foundation/'domain_certificate.json')
    bridge=load(folder/'BRIDGE901.json')if bridge_override is None else bridge_override
    lift=load(folder/'LIFT904.json')if lift_override is None else lift_override
    compact_lift=load(foundation/'BRIDGE904.json')
    need(signed['domain']=='unrestricted integers'and len(signed['variables'])==1493 and len(signed['residuals'])==1255,'whole1493/1255 integer parent')
    need(signed['variables'][:1259]==raw['variables']and signed['residuals'][:1177]==[dict(label=row['label'],terms=row['terms'])for row in raw['rows']],'all raw coordinates and coefficients retained verbatim')
    need(len(domain['guards'])==78 and domain['retained_raw_indices']==rc['retained_raw_indices'],'same full retained-body and guard count')
    need(bridge['retained_raw_indices']==rc['retained_raw_indices'],'actual raw/body forward map')
    full=dict(restored);transfers=[]
    for j,(g,t)in enumerate(zip(domain['guards'],targetdomain['guards'])):
        v,cv=g['raw_variable'],g['contracted_variable'];aux=list(range(1259+3*j,1262+3*j))
        need(g==dict(raw_variable=t['raw_variable'],contracted_variable=t['variable'],auxiliary=aux)and restored[v]==V(cv),'all78 raw/compact/guard coordinate identities')
        a,b,c=aux
        need(P(signed['residuals'][1177+j]['terms'])=={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'whole raw guard polynomial')
        transfers.append(dict(raw_variable=v,contracted_variable=cv,source_auxiliary=aux,target_auxiliary=t['auxiliary']))
        for src,dst in zip(aux,t['auxiliary']):full[src]=V(dst)
    need(bridge['guard_transfers']==transfers,'all78 raw901 witness transfers')
    projection_map=rc['retained_raw_indices']+list(range(1259,1493))
    need(bridge['source_retained_coordinates']==projection_map and len(full)==1493,'whole1493 restoration and901 forward inventory')
    for i,v in enumerate(projection_map):need(full[v]==V(i),'all901 restriction-after-restoration identities')
    rowmap=bridge['raw_row_to_target_row']
    need(len(rowmap)==1255 and sorted(i for i in rowmap if i is not None)==list(range(663))and rowmap.count(None)==592,'complete1255-to663 row partition')
    for row,tid in zip(signed['residuals'],rowmap):
        image={}
        for coefficient,monomial in row['terms']:
            term=C(coefficient)
            for v in monomial:term=mul(term,full[v])
            image=add(image,term)
        need(image==({}if tid is None else P(target['residuals'][tid]['terms'])),'every1255 original/guard row after exact affine restoration')
    expected=[]
    targets={g['raw_variable']:g['target_auxiliary']for g in compact_lift['shared_guard_transfers']}
    for g in domain['guards']:
        expected.append(dict(raw_variable=g['raw_variable'],contracted_variable=g['contracted_variable'],source_auxiliary=g['auxiliary'],target_auxiliary=targets[g['raw_variable']]))
    need(lift['copied_fixed_guard_transfers']==expected,'all78 direct raw904 fixed-value witness transfers')
    need(lift['free_witness_recipes']==compact_lift['free_witness_recipes']and lift['raw_lift_boundary']==compact_lift['raw_lift_boundary'],'same62 original-snapshot witness recipes and complete actual-use boundary')
    need(lift['fresh_new_q4_guard_record']==compact_lift['fresh_q4_guard_record']==dict(variable=303,raw_variable=657,auxiliary=[850,851,852]),'three fresh witnesses for the new q4 value only')
    need(lift['original_q4_need_not_be_nonnegative']is True and lift['all_free_recipes_read_original_tuple']is True,'no pointwise oldq4 positivity or in-place update')
    need(lift['source_body_coordinate_selection']==rc['retained_raw_indices'],'complete raw-to667 restriction after comparison lift')
    need(sorted(i for g in expected for i in g['source_auxiliary'])==list(range(1259,1493))and
         sorted([i for g in expected for i in g['target_auxiliary']]+[850,851,852])==list(range(667,904)),
         'whole raw/904 witness partitions; no omitted sign guard smuggled back')
    variants={}
    for name in ['retained','support2_affine1','support2_affine2','support4_affine2','support8_affine2']:
        variants[name]=projection(signed,load(folder/name/'equation.json'),load(folder/name/'elimination_certificate.json'))
    return {'raw_integer_restoration':restoration,'augmented_raw_guard_row_identities':1255,
            'restriction_after_restoration_identities':901,'fresh_witnesses_before_literal901':0,
            'copied_fixed_guard_triples_to904':78,'fresh_new_q4_witnesses_after_lift':3,
            'signed_projection_inverses':variants}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    folder=ROOT/'candidates/projected-radius-comparison-base'
    outcome=compact(folder)
    rejected=[]
    def reject(label,fn):
        try:fn()
        except(ValueError,KeyError,TypeError,IndexError):rejected.append(label)
        else:raise ValueError('corruption accepted: '+label)
    bad=deepcopy(load(folder/'BRIDGE904.json'));bad['fresh_q4_guard_record']['auxiliary'][0]+=1
    reject('copy original q4 witness into wrong fresh target slot',lambda:compact(folder,bridge_override=bad))
    bad=deepcopy(load(folder/'BRIDGE904.json'));bad['original_q4_need_not_be_nonnegative']=False
    reject('replace existential lift with oldq4 positivity premise',lambda:compact(folder,bridge_override=bad))
    bad=deepcopy(load(folder/'BRIDGE904.json'));bad['free_witness_recipes'][0]['expression'][2][0]='sub'
    reject('change snapshot positive comparison lift',lambda:compact(folder,bridge_override=bad))
    bad=deepcopy(load(folder/'BRIDGE904.json'));bad['shared_guard_transfers'][0]['target_auxiliary'][0]+=1
    reject('change one copied fixed-value guard witness slot',lambda:compact(folder,bridge_override=bad))
    parent=load(folder/'guarded.json');child=load(folder/'support32/equation.json')
    inverse=load(folder/'support32/elimination_certificate.json')
    bad=deepcopy(inverse);bad['steps'][0]['restoration'][0][0]+=1
    reject('change complete signed inverse',lambda:projection(parent,child,bad))
    bad=deepcopy(child);bad['residuals'][-1]['terms'][0][0]+=1
    reject('change one restored child residual coefficient',lambda:projection(parent,bad,inverse))
    rawfolder=ROOT/'candidates/retained-radius-comparison-base'
    rawoutcome=retained(rawfolder)if(rawfolder/'LIFT904.json').exists()else None
    proof_files=[folder/'PROOF.md',folder/'BRIDGE904.json',folder/'domain_certificate.json',folder/'SOURCE_PINS.json',
                 ROOT/'research/comparison-base-sign/README.md',ROOT/'research/comparison-base-sign/VERIFY.json',
                 ROOT/'research/comparison-base-sign/MANIFEST.json',ROOT/'reviews/main-root-modulus-signs-peer.py',Path(__file__)]
    if rawoutcome is not None:proof_files.extend(rawfolder/n for n in['PROOF.md','BRIDGE901.json','LIFT904.json','domain_certificate.json','SOURCE_PINS.json'])
    if rawoutcome is not None:
        bad=deepcopy(load(rawfolder/'BRIDGE901.json'));i=bad['raw_row_to_target_row'].index(None);bad['raw_row_to_target_row'][i]=0
        reject('use a raw definition row as a literal901 target row',lambda:retained(rawfolder,bridge_override=bad))
        bad=deepcopy(load(rawfolder/'LIFT904.json'));bad['fresh_new_q4_guard_record']['auxiliary'][0]+=1
        reject('reuse the wrong raw NEWq4 witness slot',lambda:retained(rawfolder,lift_override=bad))
        rawparent=load(rawfolder/'guarded.json');rawchild=load(rawfolder/'support8_affine2/equation.json')
        rawinverse=load(rawfolder/'support8_affine2/elimination_certificate.json');bad=deepcopy(rawinverse)
        bad['steps'][0]['restoration'][0][0]+=1
        reject('change raw signed inverse before all guards are restored',lambda:projection(rawparent,rawchild,bad))
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'compact':outcome,'retained':rawoutcome,
            'rejected_corruptions':rejected,
            'closed_packets':{'compact':sealed(folder),'retained':sealed(rawfolder)if rawoutcome is not None else None},
            'source_pins':{str(f.relative_to(ROOT)):sha(f)for f in proof_files},
            'scope':'Independent complete signed monic inverses in both families,592 raw affine restores,1177 original and1255 augmented row identities,78 guard rows/transfers,62 snapshot recipes and exact62/141/46 lift boundary. Ordinary chronology reviewed separately. Full SOS coefficients and native/internal-ZFC calibration are outside this focused peer.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
