#!/usr/bin/env python3
"""Power3 appended output-square frame and only its scalar-guard removal; full projections."""
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


def source_artifacts():
    pins=load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole frozen input '+name)
    baseline=ROOT/pins['parent_profile'];original=load(baseline/'source/raw_builder.json')
    old=load(baseline/'raw/parent.json');old_domain=load(baseline/'raw/domain.json')
    need((len(original['variables']),len(original['rows']),len(old['variables']),len(old['residuals']))==(1267,1185,1456,1248),'entire frozen63 RAW source/parent')
    raw=deepcopy(original);need(raw['rows'][1152]['terms'].count([-1,[106]])==1,'unique power3 output frame summand')
    raw['rows'][1152]['terms']=[[-1,[1267]] if t==[-1,[106]] else t for t in raw['rows'][1152]['terms']]
    new_variable=dict(kind='gate',name='frame.power_output_square.106')
    new_row=dict(gate=1267,label='frame_power_output_square',terms=[[-1,[106,106]],[1,[1267]]])
    raw['variables'].append(new_variable);raw['rows'].append(new_row)
    retained=[];removed=[];guards=[];variables=deepcopy(raw['variables']);residuals=[dict(label=r['label'],terms=deepcopy(r['terms'])) for r in raw['rows']]
    variable_map={i:i for i in range(1267)};guard_map=[];row_map=[[i,i] for i in range(1185)]
    for i,g in enumerate(old_domain['guards']):
        if g['predicate'].get('raw_variables')==[106]:
            need(g['predicate']['kind']=='retained_scalar','exact original power3 scalar graph')
            removed.append(i);guard_map.append([i,None]);row_map.append([1185+i,None]);continue
        j=len(guards);retained.append(i);guard_map.append([i,j]);row_map.append([1185+i,1186+j])
        fresh=deepcopy(g);fresh['auxiliary']=list(range(len(variables),len(variables)+3))
        for a,b in zip(g['auxiliary'],fresh['auxiliary']):variable_map[a]=b;variables.append(deepcopy(old['variables'][a]))
        guards.append(fresh);remap=dict(zip(g['auxiliary'],fresh['auxiliary']))
        residuals.append(dict(label=old['residuals'][1185+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in old['residuals'][1185+i]['terms']]))
    need(removed==[14] and len(guards)==62 and len(variables)==1454 and len(residuals)==1248,'only raw106 triple removed; one new body square')
    parent=deepcopy(old);parent.update(variant='power3_squared_output_frame62_raw_literal_prototype',variables=variables,residuals=residuals)
    absent=deepcopy(old_domain['inherited_absent_quotient_variables'])
    domain=dict(baseline_body_variables=1268,baseline_body_rows=1186,baseline_raw_indices=list(range(1268)),
        guards=guards,predicates=62,original_scalar_predicates=59,newly_removed_scalar_variables=[106],inherited_removed_power_output_variables=[6],inherited_absent_quotient_variables=absent,
        raw_source='source/raw_builder.json',frame_policy='FRAME_POLICY.json',radius_policy='RADIUS_POLICY.json',ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False)
    joint=next(i for i,g in enumerate(guards) if g['predicate']['kind']=='factorial_joint_lower_bound')
    radius=deepcopy(load(baseline/'RADIUS_POLICY.json'));radius['joint_guard']=dict(index=joint,predicate=guards[joint]['predicate'],auxiliary=guards[joint]['auxiliary'])
    previous=load(baseline/'FRAME_POLICY.json');ports=previous['actual_power_ports']
    policy=dict(schema='power3_output_squared_frame62_v1',actual_power_ports=ports,
        bounding_ports=[1267 if v==106 else b for v,b in zip(ports,previous['bounding_ports'])],
        newly_squared_output=dict(output=106,square_variable=1267,source_square_row=1185,changed_frame_row=1152,gate_already_present=False),
        inherited_squared_outputs=[6]+previous['inherited_range_square_outputs'],inherited_square_variables=[7]+previous['inherited_square_variables'],inherited_square_rows=[2]+previous['inherited_square_rows'],
        newly_removed_scalar_guard=106,inherited_removed_power_output_guards=[6],inherited_absent_quotient_guards=absent,
        actual_power_requests_unchanged=True,all_other_original_source_records_unchanged=True,old_frame_calibration_not_assumed=True,ordinary_source_equivalence_claimed=False,
        scope='Raw106-only RAW arithmetic prototype. One appended raw106^2 gate replaces only frame port106; actual call3 output106 and all nine earlier squared output ports remain. Ordinary signed-power/deferred-prefix/source/completeness proof is separate; no accepted metric license.')
    cuts=dict(original_source_row_map=[[i,i] for i in range(1185)],changed_source_rows=[1152],old_frame_row=original['rows'][1152],new_frame_row=raw['rows'][1152],
        added_source_variables=[dict(index=1267,variable=new_variable)],added_source_rows=[dict(index=1185,row=new_row)],
        parent_row_map=row_map,guard_index_map=guard_map,removed_guard_indices=removed,retained_guard_indices=retained,
        retained_old_variable_map=[[i,variable_map[i]] for i in sorted(variable_map)],removed_old_variables=sorted(set(range(1456))-set(variable_map)),all_other_original_source_rows_unchanged=True)
    alias=deepcopy(parent);alias['variant']='power3_squared_output_frame62_modulus_alias'
    alias['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    bridge=deepcopy(load(baseline/'CSE_BRIDGE.json'));bridge.update(identity_coordinate_bijection=list(range(1454)),unchanged_rows=[i for i in range(1248) if i!=711],old_row=parent['residuals'][711],new_row=alias['residuals'][711])
    files={'source/raw_builder.json':encoded(raw),'raw/parent.json':encoded(parent),'raw/domain.json':encoded(domain),'RADIUS_POLICY.json':encoded(radius),'FRAME_POLICY.json':encoded(policy),'CUTS.json':encoded(cuts),'cse/parent.json':encoded(alias),'CSE_BRIDGE.json':encoded(bridge)}
    return files,parent,alias,pins


def generate():
    files,parent,alias,pins=source_artifacts()
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole optimizer archive')
    census={}
    with tempfile.TemporaryDirectory(prefix='power3-square-frame-optimizer-') as tmp,zipfile.ZipFile(archive) as z:
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
        scope='Full common-radius RAW-only candidate equations/integer projections/quartics with one appended raw106 square as frame port and only the raw106 guard removed. Ordinary new-source equivalence and accepted metrics are not licensed.'))
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
