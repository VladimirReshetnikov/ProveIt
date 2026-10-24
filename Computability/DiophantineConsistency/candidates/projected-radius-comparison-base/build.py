#!/usr/bin/env python3
"""Complete78-guard901 integer quartic and fresh monic signed projections."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
NAMES=[('unprojected',0),('support4',4),('support8',8),('support16',16),('support32',32)]


def need(ok,text):
    if not ok:raise ValueError(text)


def load(path):return json.loads(path.read_text())
def digest(data):return sha256(data).hexdigest()
def encoded(v):return(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()


def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole frozen input '+n)
    base=ROOT/pins['raw_foundation'];parent_dir=ROOT/pins['foundation904'];research=ROOT/pins['base_lift_research']
    body=load(base/'source/natural667.json');old=load(parent_dir/'domain_certificate.json');audit=load(research/'VERIFY.json')
    remaining=[g for g in old['guards']if g['raw_variable']!=657]
    removed=[g for g in old['guards']if g['raw_variable']==657]
    need(len(remaining)==78 and removed==[dict(variable=303,raw_variable=657,auxiliary=[850,851,852])],'exact78 retained/one omitted q4 guard')
    equation=deepcopy(body);equation['domain']='unrestricted integers'
    equation['variant']='mixed667_78_existential_comparison_base_guards';equation.pop('metrics',None)
    guards=[]
    for j,g in enumerate(remaining):
        v=g['variable'];a,b,c=range(667+3*j,670+3*j)
        equation['variables'].extend(dict(kind='nonnegative_guard',name='guard.'+str(v)+'.'+s)for s in['a','b','c'])
        equation['residuals'].append(dict(label='guard.'+str(v),terms=[[1,[v]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]]))
        guards.append(dict(variable=v,raw_variable=g['raw_variable'],auxiliary=[a,b,c]))
    cert=dict(schema='mixed78_existential_comparison_base_guards_v1',guards=guards,
        seed_indices=[g['variable']for g in guards],removed_q4_guard_record=removed[0],
        lift_proof_sha256=digest((research/'README.md').read_bytes()),lift_audit_sha256=digest((research/'VERIFY.json').read_bytes()))
    def atom(v):return['raw',v]
    def integer(c):return['integer',c]
    def op(name,*xs):return[name,*xs]
    t=op('add',op('abs',atom(657)),integer(1));absU=op('abs',atom(655))
    Bnew=op('add',atom(667),op('mul',integer(4),atom(656),absU,t))
    recipes=[dict(raw_variable=657,expression=op('add',atom(657),op('mul',absU,t))),
        dict(raw_variable=658,expression=op('add',atom(658),op('mul',integer(4),atom(656),op('sign',atom(655)),t)))]
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json')
    for s in interfaces['seeds']:
        k=s['exponent'][1];S=op('pellChi',Bnew,atom(k));R=op('pellPsi',Bnew,atom(k))
        for key,expr in[('S',S),('R',R),('Squotient',op('exactQuotient',op('sub',S,atom(s['X'][1])),atom(655))),
            ('Rquotient',op('exactQuotient',op('sub',R,atom(k)),op('mul',integer(4),atom(s['Y'][1]))))]:
            recipes.append(dict(raw_variable=s[key][1],expression=expr))
    boundary=dict(changed_free_coordinates=audit['changed_free_coordinates'],changed_gate_rows=audit['changed_gate_rows'],
        affected_constraints=audit['affected_private_constraints'])
    slots={g['variable']:g['auxiliary']for g in old['guards']}
    bridge=dict(schema='existential901_to_literal904_v1',shared_body_coordinates=667,shared_body_rows=585,
        shared_guard_transfers=[dict(variable=g['variable'],raw_variable=g['raw_variable'],source_auxiliary=g['auxiliary'],target_auxiliary=slots[g['variable']])for g in guards],
        fresh_q4_guard_record=removed[0],all_free_recipes_read_original_tuple=True,free_witness_recipes=recipes,
        raw_lift_boundary=boundary,original_q4_need_not_be_nonnegative=True,retained_guard_values_fixed=78,
        statement='Reverse signed projections and restore all raw wires over Z. The signed-B index/residue proof first orients main roots and moduli; lift only q4/bq and comparison witnesses using existing U,V and reevaluate affected gates. All78 guarded values stay fixed. Copy78 triples and choose3 fresh witnesses for the new positive q4 value into literal904. Then its pointwise21-sign theorem extends to967. Reverse by forgetting the q4 triple; no inverse lift or same-body q4 positivity is claimed.')
    files={'domain_certificate.json':encoded(cert),'BRIDGE904.json':encoded(bridge)};census={}
    archive=REPO/pins['arithmetic_archive'];need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole arithmetic archive')
    member='ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='comparison901-produce-')as tmp:
        data=z.read(member);need(digest(data)==pins['read_source_members'][member],'literal signed optimizer')
        path=Path(tmp)/'terminal_elimination.py';path.write_bytes(data)
        spec=importlib.util.spec_from_file_location('comparison901_signed_optimizer',path)
        engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
        polynomial=engine.expand(equation)
        equation['metrics']=dict(variables=len(equation['variables']),quadratic_rows=len(equation['residuals']),
            exact_degree=max(len(m)for c,m in polynomial['terms']),expanded_monomials=len(polynomial['terms']),
            max_abs_expanded_coefficient=max(abs(c)for c,m in polynomial['terms']))
        files['guarded.json']=encoded(equation)
        for name,cap in NAMES:
            child,projection,metrics=engine.optimize(equation,max_support=cap)
            need(projection['unconstrained_removed']==[],'every integer parent coordinate uniquely restored')
            review=engine.verify(equation,child,projection)
            for filename,value in[('equation.json',child),('elimination_certificate.json',projection),
                ('expanded_polynomial.json',engine.expand(child)),
                ('BUILD.json',dict(metrics=metrics,producer_internal_verification=review,support_cap=cap))]:
                files[name+'/'+filename]=encoded(value)
            census[name]=dict(metrics=child['metrics'],support_cap=cap,
                eliminated_coordinates=len(projection['steps']),unconstrained_removed=[])
    files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
        sha256={n:digest(d)for n,d in files.items()},scope='Complete901 integer quartic and fresh signed projections. A nonpointwise comparison lift fixes78 guarded values and reaches literal904 with3 fresh q4 witnesses; its pointwise theorem then reaches967. No original-q4 positivity claim.'))
    return files,census


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,census=generate()
    for n,data in files.items():
        path=HERE/n
        if args.check:need(path.read_bytes()==data,'entire deterministic artifact '+n)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,metrics={n:d['metrics']for n,d in census.items()}),indent=2))


if __name__=='__main__':main()
