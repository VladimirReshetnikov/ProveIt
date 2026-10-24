#!/usr/bin/env python3
"""Eight squared range-output frame ports, eight quotient-guard removals and full projections."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
CONFIGS=[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),
    ('support4_affine2',4,2),('support8_affine2',8,2),('support16_affine2',16,2),
    ('support32_affine2',32,2),('support8_affine3',8,3),('support16_affine3',16,3),
    ('support32_affine3',32,3),('support8_default',8,None),('support16_default',16,None)]


def need(ok,why):
    if not ok:raise ValueError(why)


def load(path):return json.loads(path.read_bytes())
def digest(data):return sha256(data).hexdigest()
def encoded(value):return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()


OUTPUTS=[573,583,591,599,607,617,625,635]
QUOTIENTS=[575,584,592,600,609,618,627,636]
FRAME_ROWS=[1165,1167,1168,1169,1170,1172,1173,1175]


def source_artifacts():
    pins=load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole frozen input '+name)
    baseline=ROOT/pins['parent_profile'];original=load(baseline/'source/raw_builder.json')
    old=load(baseline/'raw/parent.json');old_domain=load(baseline/'raw/domain.json')
    need((len(original['variables']),len(original['rows']),len(old['variables']),len(old['residuals']))==(1259,1177,1475,1249),'entire frozen591 RAW source/parent')
    raw=deepcopy(original);newvars=list(range(1259,1267));newrows=list(range(1177,1185))
    for output,var,rowid in zip(OUTPUTS,newvars,FRAME_ROWS):
        raw['variables'].append(dict(kind='gate',name='frame.range_output_square.'+str(output)))
        raw['rows'].append(dict(gate=var,label='frame_range_output_square',terms=[[-1,[output,output]],[1,[var]]]))
        terms=raw['rows'][rowid]['terms'];need(terms.count([-1,[output]])==1,'unique actual frame-port occurrence')
        raw['rows'][rowid]['terms']=[[-1,[var]] if term==[-1,[output]] else term for term in terms]
    retained=[];removed=[];guards=[];variables=deepcopy(raw['variables']);residuals=[dict(label=r['label'],terms=deepcopy(r['terms'])) for r in raw['rows']]
    variable_map={i:i for i in range(1259)};guard_map=[];row_map=[[i,i] for i in range(1177)]
    for i,g in enumerate(old_domain['guards']):
        if g['predicate'].get('raw_variables') in [[q] for q in QUOTIENTS]:
            removed.append(i);guard_map.append([i,None]);row_map.append([1177+i,None]);continue
        j=len(guards);retained.append(i);guard_map.append([i,j]);row_map.append([1177+i,1185+j])
        fresh=deepcopy(g);fresh['auxiliary']=list(range(len(variables),len(variables)+3))
        for a,b in zip(g['auxiliary'],fresh['auxiliary']):variable_map[a]=b;variables.append(deepcopy(old['variables'][a]))
        guards.append(fresh);remap=dict(zip(g['auxiliary'],fresh['auxiliary']))
        residuals.append(dict(label=old['residuals'][1177+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in old['residuals'][1177+i]['terms']]))
    need(len(removed)==8 and len(guards)==64 and len(variables)==1459 and len(residuals)==1249,'exact eight guard triples removed; eight source squares added')
    parent=deepcopy(old);parent.update(variant='squared_range_output_frame64_raw_literal_prototype',variables=variables,residuals=residuals)
    domain=dict(baseline_body_variables=1267,baseline_body_rows=1185,baseline_raw_indices=list(range(1267)),
        guards=guards,predicates=64,original_scalar_predicates=61,removed_quotient_variables=QUOTIENTS,
        raw_source='source/raw_builder.json',frame_policy='FRAME_POLICY.json',radius_policy='RADIUS_POLICY.json',
        ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False)
    joint=next(i for i,g in enumerate(guards) if g['predicate']['kind']=='factorial_joint_lower_bound')
    radius=dict(schema='inherited_common_squared_radius_v1',factorial0=dict(input=86,output=87,radius=89,literal_definition='raw89=raw87^2'),
        factorial1=dict(input=4,output=107,radius=109,literal_definition='raw109=raw89'),
        private_squares=[dict(variable=88,row=74,literal_definition='raw88=raw86^2'),dict(variable=108,row=89,literal_definition='raw108=raw4^2')],
        unchanged_radius_rows=[75,90],joint_guard=dict(index=joint,predicate=guards[joint]['predicate'],auxiliary=guards[joint]['auxiliary']),
        ordinary_source_equivalence_claimed=False)
    ports=sorted({a[1] for call in original['powers'] for a in call.values()});squaremap=dict(zip(OUTPUTS,newvars))
    policy=dict(schema='eight_squared_range_output_frame_v1',actual_power_ports=ports,bounding_ports=[squaremap.get(v,v) for v in ports],
        replaced_outputs=OUTPUTS,square_variables=newvars,square_rows=newrows,changed_frame_rows=FRAME_ROWS,
        removed_quotient_guards=QUOTIENTS,actual_power_requests_unchanged=True,
        all_other_original_source_metadata_and_records_unchanged=True,appended_squares_need_no_input_signs=True,
        original_numeric_gate_order_is_not_a_chronological_premise=True,
        old_frame_calibration_not_assumed=True,ordinary_source_equivalence_claimed=False,
        scope='Eight-only RAW arithmetic prototype. Squared bounding ports replace only the eight possibly signed range outputs in W. Ordinary source/semantics/completeness are separate; no accepted metric license.')
    cuts=dict(original_source_row_map=[[i,i] for i in range(1177)],changed_source_rows=FRAME_ROWS,
        appended_square_rows=newrows,appended_square_variables=newvars,
        old_frame_rows={str(i):original['rows'][i] for i in FRAME_ROWS},new_frame_rows={str(i):raw['rows'][i] for i in FRAME_ROWS},
        parent_row_map=row_map,guard_index_map=guard_map,removed_guard_indices=removed,retained_guard_indices=retained,
        retained_old_variable_map=[[i,variable_map[i]] for i in sorted(variable_map)],
        removed_old_variables=sorted(set(range(1475))-set(variable_map)),all_other_original_source_rows_unchanged=True)
    alias=deepcopy(parent);alias['variant']='squared_range_output_frame64_modulus_alias'
    alias['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    bridge=deepcopy(load(baseline/'CSE_BRIDGE.json'));bridge.update(identity_coordinate_bijection=list(range(1459)),old_row=parent['residuals'][711],new_row=alias['residuals'][711])
    files={'source/raw_builder.json':encoded(raw),'raw/parent.json':encoded(parent),'raw/domain.json':encoded(domain),
        'RADIUS_POLICY.json':encoded(radius),'FRAME_POLICY.json':encoded(policy),'CUTS.json':encoded(cuts),
        'cse/parent.json':encoded(alias),'CSE_BRIDGE.json':encoded(bridge)}
    return files,parent,alias,pins


def generate():
    files,parent,alias,pins=source_artifacts()
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole optimizer archive')
    census={}
    with tempfile.TemporaryDirectory(prefix='squared-radius-raw-optimizer-') as tmp,zipfile.ZipFile(archive) as z:
        for name,h in pins['members'].items():need(digest(z.read(name))==h,'whole reviewed engine member '+name)
        name=next(name for name in pins['members'] if name.endswith('/terminal_elimination.py'))
        path=Path(tmp)/'engine.py';path.write_bytes(z.read(name))
        spec=importlib.util.spec_from_file_location('reviewed_squared_radius_monic_engine',path)
        engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
        for mode,full in [('raw',parent),('cse',alias)]:
            for name,cap,affine in CONFIGS:
                out,cert,metrics=engine.optimize(full,max_support=cap,affine_support=affine)
                need(cert['unconstrained_removed']==[],'no unconstrained integer coordinate discarded')
                engine.verify(full,out,cert)
                prefix=mode+'/'+name
                files[prefix+'/equation.json']=encoded(out)
                files[prefix+'/projection.json']=encoded(cert)
                files[prefix+'/polynomial.json']=encoded(engine.expand(out))
                census[prefix]=dict(metrics=out['metrics'],support_cap=cap,affine_cap=affine,
                    unique_signed_restorations=len(cert['steps']),unconstrained_removed=[],
                    ordinary_source_equivalence_claimed=False)
                print(prefix,json.dumps(out['metrics'],sort_keys=True),flush=True)
    files['CENSUS.json']=encoded(census)
    files['BUILD.json']=encoded(dict(generator_sha256=digest(Path(__file__).read_bytes()),
        source_pins_sha256=digest((HERE/'SOURCE_PINS.json').read_bytes()),
        files={name:digest(data) for name,data in files.items()},
        scope='Full common-radius RAW-only candidate equations/integer projections/quartics with eight squared frame ports and eight removed quotient guards. Ordinary new-source equivalence and accepted metrics are not licensed.'))
    return files,census


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--check',action='store_true')
    group.add_argument('--source-only',action='store_true')
    args=parser.parse_args()
    if args.source_only:files,_,_,_=source_artifacts();census={}
    else:files,census=generate()
    for name,data in files.items():
        path=HERE/name
        if args.check:need(path.is_file() and path.read_bytes()==data,'deterministic complete artifact '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,source_only=args.source_only,raw_profiles=len(census),ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
