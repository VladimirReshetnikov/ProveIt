#!/usr/bin/env python3
"""RAW-only common F² radius, joint factorial guard and certified modulus sharing."""
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


def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole frozen input '+name)
    baseline=ROOT/pins['parent_profile']
    original=load(baseline/'source/raw_builder.json');raw=deepcopy(original)
    need(len(raw['variables'])==1259 and len(raw['rows'])==1177 and raw['rows'][90]==dict(
        gate=109,label='multiplication',terms=[[-1,[107,108]],[1,[109]]]), 'exact original second radius gate')
    raw['rows'][90]['terms']=[[-1,[89]],[1,[109]]]
    old=load(baseline/'raw/parent.json');old_domain=load(baseline/'raw/domain.json')
    need(len(old['variables'])==1475 and len(old['residuals'])==1249 and len(old_domain['guards'])==72,'entire frozen594 RAW parent')
    parent=deepcopy(old);parent['variant']='common_squared_radius_joint_guard_raw72_literal_prototype'
    parent['residuals'][90]['terms']=deepcopy(raw['rows'][90]['terms'])
    guards=deepcopy(old_domain['guards'])
    need(guards[71]['predicate']==dict(kind='factorial_index_lower_bound',raw_variables=[87,86],terms=[[1,[87]],[-1,[86]]]),'exact frozen final f-K predicate')
    guards[71]['predicate']=dict(kind='factorial_joint_lower_bound',raw_variables=[87,86,107],terms=[[1,[87]],[-1,[86]],[-1,[107]]])
    a,b,c=guards[71]['auxiliary']
    parent['residuals'][1248]['terms']=deepcopy(guards[71]['predicate']['terms'])+[
        [-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]
    domain=dict(baseline_body_variables=1259,baseline_body_rows=1177,
        baseline_raw_indices=list(range(1259)),guards=guards,predicates=72,
        original_scalar_predicates=69,changed_guard_index=71,
        raw_source='source/raw_builder.json',radius_policy='RADIUS_POLICY.json',
        ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False)
    policy=dict(schema='literal_common_squared_radius_policy_v2',
        factorial0=dict(input=86,output=87,radius=89,literal_definition='raw89=raw87^2',unchanged=True),
        factorial1=dict(input=4,output=107,radius=109,literal_definition='raw109=raw89',source_row=90),
        retained_private_squares=[dict(variable=88,source_row=74,literal_definition='raw88=raw86^2'),
            dict(variable=108,source_row=89,literal_definition='raw108=raw4^2')],
        changed_predicate=dict(index=71,literal_definition='raw87-raw86-raw107>=0',auxiliary=[a,b,c]),
        raw825_guard_restored=False,duplicated_base_definitions_retained_in_raw=dict(first=92,second=112,first_row=77,second_row=92),
        separate_modulus_alias_bridge='CSE_BRIDGE.json',legacy_raw_metadata_retained_verbatim_except_row90=True,
        metadata_is_not_a_calibration_license=True,
        scope='RAW arithmetic prototype only. No source equivalence, compiler/radix completeness, compact bridge, or accepted metric license. The separate CSE bridge is a universal integer row identity, not a calibration.')
    cuts=dict(source_row_map=[[i,i] for i in range(1177)],changed_source_row=90,
        old_source_row=original['rows'][90],new_source_row=raw['rows'][90],
        parent_row_map=[[i,i] for i in range(1249)],changed_parent_rows=[90,1248],
        guard_index_map=[[i,i] for i in range(72)],changed_guard_index=71,
        old_guard=old_domain['guards'][71],new_guard=guards[71],old_guard_row=old['residuals'][1248],new_guard_row=parent['residuals'][1248],
        variables_unchanged=True,all_other_source_and_parent_records_unchanged=True)
    alias=deepcopy(parent);alias['variant']='common_squared_radius_joint_guard_modulus_alias72'
    alias['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    q=[[1,[112]],[1,[92]],[-1,[695]]];minusq=[[-c,m] for c,m in q]
    coefficients={str(i):[[c,[]]] for i,c in [(711,-1),(707,1),(708,-1),(709,-1),(710,-1),(673,-1),(674,1),(675,1),(676,1),(677,1)]}
    coefficients.update({'90':minusq,'92':minusq,'77':q})
    bridge=dict(schema='common_radius_unit_row_operation_v1',source='raw/parent.json',target='cse/parent.json',
        replaced_row=711,pivot_coefficient=-1,old_row=parent['residuals'][711],new_row=alias['residuals'][711],
        identity_coefficients=coefficients,unchanged_rows=[i for i in range(1249) if i!=711],
        identity_coordinate_bijection=list(range(1475)),
        base_alias_identity=dict(terms=[[1,[112]],[-1,[92]]],row_coefficients={'90':1,'92':1,'77':-1}),
        meaning='new711=sum(coefficients*oldrows); old711=-new711+the unchanged-row sum. Both directions are polynomial identities over unrestricted integers; every other row and coordinate is retained.')
    files={'source/raw_builder.json':encoded(raw),'raw/parent.json':encoded(parent),
        'raw/domain.json':encoded(domain),'RADIUS_POLICY.json':encoded(policy),'CUTS.json':encoded(cuts),
        'cse/parent.json':encoded(alias),'CSE_BRIDGE.json':encoded(bridge)}
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
        scope='Full common-radius RAW-only candidate equations/integer projections/quartics with the joint f-K-g guard and universal modulus-alias bridge. Ordinary new-source equivalence and accepted metrics are not licensed.'))
    return files,census


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    files,census=generate()
    for name,data in files.items():
        path=HERE/name
        if args.check:need(path.is_file() and path.read_bytes()==data,'deterministic complete artifact '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,raw_profiles=len(census),
        ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
