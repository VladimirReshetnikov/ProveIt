#!/usr/bin/env python3
"""Optimizer-free literal RAW deltas, all integer projections and full quartics."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
import zipfile

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos


def need(ok,why):
    if not ok:raise ValueError(why)


def load(path):return json.loads(path.read_bytes())
def digest(data):return sha256(data).hexdigest()


def sealed(folder):
    manifest=folder/'MANIFEST.json'
    if not manifest.exists():return
    records=load(manifest)['files']
    need(set(records)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=manifest},'closed full packet inventory '+str(folder))
    for name,h in records.items():need(digest((folder/name).read_bytes())==h,'whole sealed member '+name)


def literal(original,raw,old,old_domain,parent,domain,cuts,policy):
    need(len(original['variables'])==1259 and len(original['rows'])==1177,'entire original raw body size')
    need(original['rows'][75]==dict(gate=89,label='multiplication',terms=[[-1,[87,88]],[1,[89]]]),'actual original output-linear radius gate')
    want=deepcopy(original);want['rows'][75]['terms']=[[-1,[87,87]],[1,[89]]]
    need(raw==want,'complete source JSON changes only radius row75; all metadata/other rows literal')
    need(raw['rows'][74]==dict(gate=88,label='multiplication',terms=[[-1,[86,86]],[1,[88]]]),'private K-square row74 remains unchanged')
    need([i for i,r in enumerate(raw['rows']) if any(88 in m for c,m in r['terms'])]==[74], 'raw88 now uniquely defined private wire, retained explicitly')
    n,nr=old_domain['baseline_body_variables'],old_domain['baseline_body_rows']
    need((n,nr)==(1259,1177) and old_domain['baseline_raw_indices']==list(range(1259)),'RAW body uses all original coordinate indices')
    need(old['variables'][:n]==original['variables'] and old['residuals'][:nr]==[
        dict(label=r['label'],terms=r['terms']) for r in original['rows']], 'entire frozen72 RAW body binding')
    need(len(old['variables'])==1475 and len(old['residuals'])==1249 and len(old_domain['guards'])==72,'full frozen72 RAW parent shape')
    guards=deepcopy(old_domain['guards'])
    need(guards[71]['predicate']==dict(kind='factorial_lower_bound',raw_variables=[87],terms=[[1,[87]],[-2,[]]])
         and guards[71]['auxiliary']==[1472,1473,1474], 'exact old final factorial predicate and triple')
    guards[71]['predicate']=dict(kind='factorial_index_lower_bound',raw_variables=[87,86],terms=[[1,[87]],[-1,[86]]])
    expected=deepcopy(old);expected['variant']='squared_radius_f_ge_K_raw72_literal_prototype'
    expected['residuals'][75]['terms']=[[-1,[87,87]],[1,[89]]]
    expected['residuals'][1248]['terms']=[[1,[87]],[-1,[86]],[-1,[1472,1472]],[-1,[1473,1473]],[-1,[1474,1474]],[-1,[1474]]]
    need(parent==expected,'complete full parent: only row75/final guard change, same variables/labels/other rows')
    expected_domain=dict(baseline_body_variables=1259,baseline_body_rows=1177,baseline_raw_indices=list(range(1259)),
        guards=guards,predicates=72,original_scalar_predicates=69,changed_guard_index=71,
        raw_source='source/raw_builder.json',radius_policy='RADIUS_POLICY.json',
        ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False)
    need(domain==expected_domain,'entire72-guard domain: same69 scalar and V/product, same triples, only f-K predicate exchanged')
    need(len([g for g in guards if g['predicate']['kind']=='retained_scalar'])==69,'exact69 unchanged scalar predicates')
    need(cuts==dict(source_row_map=[[i,i] for i in range(1177)],changed_source_row=75,
        old_source_row=original['rows'][75],new_source_row=raw['rows'][75],
        parent_row_map=[[i,i] for i in range(1249)],changed_parent_rows=[75,1248],
        guard_index_map=[[i,i] for i in range(72)],changed_guard_index=71,
        old_guard=old_domain['guards'][71],new_guard=guards[71],old_guard_row=old['residuals'][1248],
        new_guard_row=parent['residuals'][1248],variables_unchanged=True,
        all_other_source_and_parent_records_unchanged=True), 'all original source/body/guard row maps and exact changed operands')
    need(policy==dict(schema='literal_squared_radius_policy_v1',factorial0=dict(input=86,output=87,radius=89,
        literal_definition='raw89=raw87^2',source_row=75),factorial1=dict(input=4,output=107,radius=109,
        literal_definition='raw109=raw107*raw4^2',unchanged=True),
        retained_private_square=dict(variable=88,source_row=74,literal_definition='raw88=raw86^2'),
        changed_predicate=dict(index=71,literal_definition='raw87-raw86>=0',auxiliary=[1472,1473,1474]),
        legacy_raw_metadata_retained_verbatim_except_row75=True,legacy_radius_mode=original['radius_mode'],
        metadata_is_not_a_calibration_license=True,
        scope='RAW arithmetic prototype only. No source equivalence, compiler/radix completeness, compact bridge, native/internal-ZFC, or accepted metric license.'), 'complete explicit new policy; legacy metadata supplies no old calibration')
    return dict(original_source_rows=1177,parent_rows=1249,guard_predicates=72,unchanged_scalar_predicates=69,
        changed_source_rows=[75],changed_parent_rows=[75,1248],retained_private_square88=True,
        factorial1_radius_unchanged=True,all_variables_and_other_records_unchanged=True)


def evaluate(terms,values):
    result=0
    for c,m in terms:
        for v in m:c*=values[v]
        result+=c
    return result


def signed_controls(parent,child,certificate):
    for seed in range(3):
        values=[None]*len(parent['variables'])
        for j,v in enumerate(certificate['retained_original_variables']):values[v]=((j+2)*5+seed)%7-3
        for step in reversed(certificate['steps']):
            need(all(values[v] is not None for c,m in step['restoration'] for v in m),'every signed restoration operand already recovered')
            values[step['variable']]=evaluate(step['restoration'],values)
        need(all(v is not None for v in values),'every integer parent coordinate restored')
        reduced=[values[v] for v in certificate['retained_original_variables']]
        for j,rid in enumerate(certificate['retained_original_rows']):
            need(evaluate(parent['residuals'][rid]['terms'],values)==evaluate(child['residuals'][j]['terms'],reduced),'every signed surviving row agrees')
        removed=set(range(len(parent['residuals'])))-set(certificate['retained_original_rows'])
        need(all(evaluate(parent['residuals'][rid]['terms'],values)==0 for rid in removed),'every removed defining/zero residual restored')
    return 3


def complete_quartic(out,quartic):
    measured=full_sos(out,quartic)
    measured['max_abs_row_coefficient']=max(abs(c) for row in out['residuals'] for c,m in row['terms'])
    measured['variable_kinds']=dict(Counter(v['kind'] for v in out['variables']))
    need(out['metrics']==measured,'every actual census field independently remeasured')
    return measured


def reject(name,action):
    try:action()
    except (ValueError,RuntimeError,KeyError,TypeError,IndexError):return name
    raise ValueError('corruption accepted '+name)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    sealed(HERE)
    pins=load(HERE/'SOURCE_PINS.json')
    need(pins['ordinary_source_equivalence_claimed'] is False and pins['compact_bridge_assumed'] is False,'explicit non-calibration prototype boundary')
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole immutable source input '+name)
    old_folder=ROOT/pins['parent_profile'];sealed(old_folder)
    build=load(HERE/'BUILD.json')
    need(build['generator_sha256']==digest((HERE/'build.py').read_bytes()) and
         build['source_pins_sha256']==digest((HERE/'SOURCE_PINS.json').read_bytes()), 'producer and complete input pins')
    for name,h in build['files'].items():need(digest((HERE/name).read_bytes())==h,'whole generated source/equation/inverse/quartic '+name)
    original=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    raw=load(HERE/'source/raw_builder.json');old=load(old_folder/'raw/parent.json');old_domain=load(old_folder/'raw/domain.json')
    parent=load(HERE/'raw/parent.json');domain=load(HERE/'raw/domain.json');cuts=load(HERE/'CUTS.json');policy=load(HERE/'RADIUS_POLICY.json')
    inputs=(original,raw,old,old_domain,parent,domain,cuts,policy)
    binding=literal(*inputs);mutations=[]
    def changed(position,mutation):
        values=list(inputs);values[position]=deepcopy(values[position]);mutation(values[position]);return lambda:literal(*values)
    mutations.append(reject('old output-linear radius retained',changed(1,lambda x:x['rows'][75].update(terms=[[-1,[87,88]],[1,[89]]]))))
    mutations.append(reject('private88 wire or row74 altered',changed(1,lambda x:x['rows'][74].update(terms=[[-1,[87,87]],[1,[88]]]))))
    mutations.append(reject('factorial1 radius changed',changed(1,lambda x:x['new_factorial_data'][1].update(radius=['v',89]))))
    mutations.append(reject('weaken exchanged guard back to f>=2',changed(4,lambda x:x['residuals'][1248].update(terms=old['residuals'][1248]['terms']))))
    mutations.append(reject('change unrelated original row coefficient',changed(4,lambda x:x['residuals'][0]['terms'][0].__setitem__(0,-2))))
    mutations.append(reject('change surviving guard auxiliary metadata',changed(4,lambda x:x['variables'][1474].update(name='altered auxiliary'))))
    mutations.append(reject('claim ordinary equivalence from literal delta',changed(5,lambda x:x.update(ordinary_source_equivalence_claimed=True))))
    mutations.append(reject('claim a compact bridge',changed(5,lambda x:x.update(compact_bridge_assumed=True))))
    mutations.append(reject('lose complete guard row map',changed(6,lambda x:x['guard_index_map'].__setitem__(71,[71,70]))))
    mutations.append(reject('treat inherited headers as calibration',changed(7,lambda x:x.update(metadata_is_not_a_calibration_license=False))))
    settings={'raw/'+name:(cap,affine) for name,cap,affine in [
        ('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),('support4_affine2',4,2),
        ('support8_affine2',8,2),('support16_affine2',16,2),('support32_affine2',32,2),
        ('support8_affine3',8,3),('support16_affine3',16,3),('support32_affine3',32,3),
        ('support8_default',8,None),('support16_default',16,None)]}
    census=load(HERE/'CENSUS.json');need(set(census)==set(settings),'all twelve explicit RAW configurations only')
    old_census=load(old_folder/'CENSUS.json')
    comparison=[]
    for name,record in sorted(census.items()):
        a,b=old_census[name]['metrics'],record['metrics']
        comparison.append(dict(configuration=name,old72_literal_metrics=a,new_prototype_metrics=b,
            delta={k:b[k]-a[k] for k in ['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient']},
            ordinary_source_equivalence_claimed=False))
    need(load(HERE/'MEASURED_COMPARISON.json')==dict(
        scope='Measured arithmetic prototypes only; no old/new source zero-equivalence or accepted metric license.',
        comparisons=comparison), 'entire independently checked literal prototype comparison; no semantic improvement asserted')
    need(not (HERE/'compact').exists(),'no compact equation or bridge supplied')
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole reviewed projection archive')
    results={}
    with tempfile.TemporaryDirectory(prefix='squared-radius-independent-projection-') as tmp,zipfile.ZipFile(archive) as z:
        for name,h in pins['members'].items():need(digest(z.read(name))==h,'whole reviewed archive member '+name)
        for filename in ['verify_projection.py','independent_polynomial.py','audit_common_radix.py']:
            member=next(n for n in pins['members'] if n.endswith('/'+filename))
            (Path(tmp)/filename).write_bytes(z.read(member))
        sys.path.insert(0,str(tmp))
        from verify_projection import verify
        for name,record in census.items():
            need((record['support_cap'],record['affine_cap'])==settings[name] and
                 record['ordinary_source_equivalence_claimed'] is False, 'exact settings and research-only status')
            out=load(HERE/name/'equation.json');cert=load(HERE/name/'projection.json');quartic=load(HERE/name/'polynomial.json')
            need(cert['unconstrained_removed']==record['unconstrained_removed']==[] and
                 len(cert['steps'])==record['unique_signed_restorations'] and out['metrics']==record['metrics'], 'whole signed restoration/metric ledger')
            results[name]=dict(projection=verify(parent,out,cert),full_quartic=complete_quartic(out,quartic),signed_fixture_count=signed_controls(parent,out,cert))
            if cert['steps']:
                bad=deepcopy(cert);bad['steps'][0]['restoration'][0][0]+=1
                mutations.append(reject('alter signed inverse '+name,lambda:verify(parent,out,bad)))
            bad=deepcopy(quartic);bad['terms'][0][0]+=1
            mutations.append(reject('alter full quartic coefficient '+name,lambda:complete_quartic(out,bad)))
            bad_out=deepcopy(out);bad_out['metrics']['max_abs_row_coefficient']+=1
            mutations.append(reject('alter independently measured row height '+name,lambda:complete_quartic(bad_out,quartic)))
        need(not any('terminal_elimination' in k or 'monic_engine' in k for k in sys.modules),'optimizer was not imported')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_raw_binding=binding,profiles=results,
        rejected_corruptions=mutations,optimizer_imported=False,compact_bridge_assumed=False,
        ordinary_source_equivalence_claimed=False,accepted_metrics_promoted=False,lean_run=False,
        source_pins={name:digest((HERE/name).read_bytes()) for name in ['README.md','SOURCE_PINS.json','BUILD.json','RADIUS_POLICY.json','CUTS.json','MEASURED_COMPARISON.json','check.py']},
        scope='Exact RAW source/guard delta, whole unrestricted-integer monic projection equivalences to the NEW parent and independent complete quartics/censuses only. No ordinary compiler/radix/source calibration or accepted metric license.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',raw_profiles=len(results),corruptions=len(mutations),ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
