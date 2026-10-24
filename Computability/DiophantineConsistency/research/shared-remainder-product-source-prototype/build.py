#!/usr/bin/env python3
"""Six shared-remainder product guards; full RAW/CSE projections after ordinary licensing."""
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
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole immutable input '+n)
    ordinary=ROOT/pins['ordinary_packet'];baseline=ROOT/pins['parent_profile']
    need(digest((ordinary/'MANIFEST.json').read_bytes())==pins['ordinary_manifest_sha256'],'whole ordinary56 seal')
    parent=load(ordinary/'raw/parent.json');domain=load(ordinary/'raw/domain.json');certificate=load(ordinary/'CERTIFICATE.json')
    need((len(parent['variables']),len(parent['residuals']),len(domain['guards']))==(1436,1242,56),'complete accepted shared56 parent')
    copied=['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CUTS.json','CERTIFICATE.json','PROOF.md','BOUNDARY.md']
    files={n:(ordinary/n).read_bytes() for n in copied}
    files['FRAME_IDENTITIES.json']=(baseline/'FRAME_IDENTITIES.json').read_bytes()
    policy=dict(schema='shared_remainder_product_guards56_finite_binding_v1',ordinary_packet=pins['ordinary_packet'],ordinary_manifest_sha256=pins['ordinary_manifest_sha256'],copied_ordinary_files=copied,
        arithmetic_body_unchanged_from_baseline=True,raw_parent_and_domain_byte_identical_to_ordinary=True,new_body_gates=0,
        replaced_scalar_pairs=[x['pair'] for x in certificate['exchanges']],retained_anchor_pairs=[g['anchor'] for g in certificate['groups']],
        body_coordinates=1268,body_rows=1186,predicates=56,retained_scalar_predicates=47,new_product_predicates=6,preserved_replacement_predicates=3,
        raw_body_projection='identity',guard_auxiliaries_reconstructed_existentially=True,whole_guarded_tuple_bijection_assumed=False,
        ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False,accepted_metrics_promoted=False,
        scope='Finite complete RAW/CSE algebra/projection/quartic candidate. Ordinary same-body guard-domain equivalence comes only from the separately sealed ordinary packet. No projected count is inferred from guard removal.')
    files['GUARD_POLICY.json']=encoded(policy)
    target=deepcopy(parent);target['variant']='shared_remainder_product_guards56_modulus_alias'
    target['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    bridge=deepcopy(load(baseline/'CSE_BRIDGE.json'));bridge.update(identity_coordinate_bijection=list(range(1436)),unchanged_rows=[i for i in range(1242) if i!=711],old_row=parent['residuals'][711],new_row=target['residuals'][711])
    files['cse/parent.json']=encoded(target);files['CSE_BRIDGE.json']=encoded(bridge)
    return files,parent,target,pins


def generate():
    files,parent,alias,pins=source_artifacts()
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole optimizer archive')
    census={}
    with tempfile.TemporaryDirectory(prefix='shared-remainder-product-optimizer-') as tmp,zipfile.ZipFile(archive) as z:
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
        scope='Full shared-remainder-product RAW/CSE equations, integer projections and complete quartics. The same-body ordinary source theorem is separately sealed; accepted metric promotion is not inferred by this producer.'))
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
