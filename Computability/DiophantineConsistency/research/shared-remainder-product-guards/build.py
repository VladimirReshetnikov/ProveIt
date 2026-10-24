#!/usr/bin/env python3
"""Materialize only the full literal shared-remainder guard replacement; no optimizer."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
# Each group has one retained direct anchor and its exact source sum cuts.
GROUPS=[dict(denominator=574,anchor=[576,577],pairs=[[576,577],[585,586],[593,594],[601,602]],rows=[[547,548,549],[553,554,555],[559,560,561],[565,566,567]]),
 dict(denominator=608,anchor=[610,611],pairs=[[610,611],[619,620]],rows=[[572,573,574],[578,579,580]]),
 dict(denominator=626,anchor=[628,629],pairs=[[628,629],[637,638]],rows=[[585,586,587],[591,592,593]]),
 dict(denominator=547,anchor=[549,550],pairs=[[549,550],[562,563]],rows=[[526,527,528],[537,538,539]])]
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(b):return sha256(b).hexdigest()
def encoded(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'frozen whole input '+n)
    base=ROOT/pins['accepted_profile_packet'];raw=load(base/'source/raw_builder.json');old=load(base/'raw/parent.json');domain=load(base/'raw/domain.json')
    need((len(raw['variables']),len(raw['rows']),len(old['variables']),len(old['residuals']),len(domain['guards']))==(1268,1186,1454,1248,62),'entire accepted62 literal boundary')
    singles={g['predicate']['raw_variables'][0]:i for i,g in enumerate(domain['guards']) if g['predicate']['kind']=='retained_scalar'}
    groups=deepcopy(GROUPS);exchanges=[];byfirst={};bysecond={}
    for group in groups:
        group['anchor_guard_indices']=[singles[v] for v in group['anchor']]
        group['source_sum_cuts']=[]
        for pair,rows in zip(group['pairs'],group['rows']):
            group['source_sum_cuts'].append(dict(pair=pair,polynomial=[[1,[group['denominator']]],[-1,[pair[0]]],[-1,[pair[1]]],[-1,[]]],row_combination=[dict(row=i,multiplier=[[1,[]]]) for i in rows]))
            if pair==group['anchor']:continue
            item=dict(pair=pair,denominator=group['denominator'],anchor=group['anchor'],old_guard_indices=[singles[v] for v in pair],source_sum_rows=rows,anchor_sum_rows=group['rows'][0])
            item['sum_difference_cut']=dict(polynomial=[[1,[pair[0]]],[1,[pair[1]]],[-1,[group['anchor'][0]]],[-1,[group['anchor'][1]]]],row_combination=[dict(row=i,multiplier=[[1,[]]]) for i in group['rows'][0]]+[dict(row=i,multiplier=[[-1,[]]]) for i in rows])
            exchanges.append(item);byfirst[item['old_guard_indices'][0]]=item;bysecond[item['old_guard_indices'][1]]=item
    variables=deepcopy(raw['variables']);residuals=deepcopy(old['residuals'][:1186]);guards=[];variable_map={i:i for i in range(1268)};retained_rows=[[i,i] for i in range(1186)];retained_indices=[];guard_map=[]
    for i,g in enumerate(domain['guards']):
        if i in bysecond:
            item=bysecond[i];guard_map.append(dict(old_index=i,new_index=item['new_guard_index'],kind='replaced_pair_member'));continue
        j=len(guards);aux=list(range(len(variables),len(variables)+3))
        if i in byfirst:
            item=byfirst[i];r,s=item['pair'];label='shared_remainder_product.'+str(r)+'.'+str(s)
            variables.extend(dict(kind='nonnegative_guard',name=label+'.'+a) for a in ['a','b','c'])
            predicate=dict(kind='shared_remainder_product',raw_variables=[r,s],terms=[[1,[r,s]]])
            a,b,c=aux;row=dict(label=label,terms=[[1,[r,s]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])
            item.update(new_guard_index=j,new_auxiliary=aux,new_parent_row=1186+j,old_auxiliary_groups=[domain['guards'][k]['auxiliary'] for k in item['old_guard_indices']],old_parent_rows=[1186+k for k in item['old_guard_indices']])
            guard_map.append(dict(old_index=i,new_index=j,kind='replaced_pair_member'))
        else:
            predicate=deepcopy(g['predicate']);remap=dict(zip(g['auxiliary'],aux))
            for a,b in zip(g['auxiliary'],aux):variable_map[a]=b;variables.append(deepcopy(old['variables'][a]))
            row=dict(label=old['residuals'][1186+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in old['residuals'][1186+i]['terms']])
            retained_rows.append([1186+i,1186+j]);retained_indices.append(i);guard_map.append(dict(old_index=i,new_index=j,kind='retained'))
        guards.append(dict(auxiliary=aux,predicate=predicate));residuals.append(row)
    need((len(variables),len(residuals),len(guards))==(1436,1242,56),'full new literal parent dimensions')
    parent=deepcopy(old);parent.update(variant='shared_remainder_product_guards56_raw_literal',variables=variables,residuals=residuals)
    newdomain=dict(baseline_body_variables=1268,baseline_body_rows=1186,baseline_raw_indices=list(range(1268)),guards=guards,predicates=56,original_scalar_predicates=47,shared_remainder_product_predicates=6,
        replaced_scalar_pairs=[x['pair'] for x in exchanges],retained_anchor_pairs=[g['anchor'] for g in groups],inherited_removed_power_output_variables=[6,106],inherited_absent_quotient_variables=domain['inherited_absent_quotient_variables'],
        raw_source='source/raw_builder.json',frame_policy='FRAME_POLICY.json',radius_policy='RADIUS_POLICY.json',guard_policy='CERTIFICATE.json',compact_bridge_assumed=False,ordinary_source_equivalence_proved_separately=True)
    radius=deepcopy(load(base/'RADIUS_POLICY.json'));joint=next(i for i,g in enumerate(guards) if g['predicate']['kind']=='factorial_joint_lower_bound');radius['joint_guard']=dict(index=joint,predicate=guards[joint]['predicate'],auxiliary=guards[joint]['auxiliary'])
    cuts=dict(source_row_map=[[i,i] for i in range(1186)],source_variables_unchanged=True,source_rows_unchanged=True,retained_parent_rows=retained_rows,guard_index_map=guard_map,retained_old_guard_indices=retained_indices,
        replaced_guard_indices=sorted(set(byfirst)|set(bysecond)),retained_old_variable_map=[[i,variable_map[i]] for i in sorted(variable_map)],removed_old_auxiliary=sorted(set(range(1454))-set(variable_map)),new_product_auxiliary=sorted(a for x in exchanges for a in x['new_auxiliary']),
        auxiliary_zero_sets_identified_pointwise=False,raw_coordinate_projection='identity',quantification='For each unrestricted integer tuple satisfying the unchanged1186 body residuals, existence of old62guard witnesses iff existence of new56guard witnesses.')
    certificate=dict(schema='shared_remainder_product_guard_equivalence_v1',body_variables=1268,body_rows=1186,old_parent_variables=1454,old_parent_rows=1248,old_predicates=62,new_parent_variables=1436,new_parent_rows=1242,new_predicates=56,retained_scalars=47,new_product_predicates=6,
        groups=groups,exchanges=exchanges,legendre_graph=dict(polynomial='u-a^2-b^2-c^2-c',auxiliary_domain='all integers',represented_values='all nonnegative integers'),raw_body_byte_unchanged=True,all_power_and_frame_ports_unchanged=True,full_old_numerical_endpoint_inherited=True,
        direct_anchor_signs_used_before_product_restoration=True,nonnegative_denominators_not_assumed=True,positive_pair_or_pell_semantics_used=False,ordinary_equivalence_proof='PROOF.md',projected_metrics_claimed=False,new_lean_claim=False)
    files={'source/raw_builder.json':(base/'source/raw_builder.json').read_bytes(),'raw/parent.json':encoded(parent),'raw/domain.json':encoded(newdomain),'FRAME_POLICY.json':(base/'FRAME_POLICY.json').read_bytes(),'RADIUS_POLICY.json':encoded(radius),'CUTS.json':encoded(cuts),'CERTIFICATE.json':encoded(certificate)}
    files['BUILD.json']=encoded(dict(generator_sha256=digest(Path(__file__).read_bytes()),source_pins_sha256=digest((HERE/'SOURCE_PINS.json').read_bytes()),files={n:digest(b) for n,b in files.items()},scope='Only whole literal body/guard materialization and polynomial cut ledgers. No optimizer or projected census.'))
    return files

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    for n,b in generate().items():
        path=HERE/n
        if args.check:need(path.is_file() and path.read_bytes()==b,'deterministic whole artifact '+n)
        else:path.parent.mkdir(exist_ok=True,parents=True);path.write_bytes(b)
    print(json.dumps(dict(status='PASS',check=args.check,body_unchanged=True,predicates=56,optimizer_executed=False),sort_keys=True))
if __name__=='__main__':main()
