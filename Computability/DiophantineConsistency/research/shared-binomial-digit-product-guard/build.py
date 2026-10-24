#!/usr/bin/env python3
"""Materialize one derived-anchor binomial digit product guard; stdlib only."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(b):return sha256(b).hexdigest()
def encoded(v):return (json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def cut(polynomial,positive,negative=()):return dict(polynomial=polynomial,row_combination=[dict(row=i,multiplier=[[1,[]]]) for i in positive]+[dict(row=i,multiplier=[[-1,[]]]) for i in negative])
def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'entire frozen input '+n)
    base=ROOT/pins['accepted_profile_packet'];raw=load(base/'source/raw_builder.json');old=load(base/'raw/parent.json');domain=load(base/'raw/domain.json')
    need((len(raw['variables']),len(raw['rows']),len(old['variables']),len(old['residuals']),len(domain['guards']))==(1268,1186,1436,1242,56),'whole accepted56 boundary')
    singles={g['predicate']['raw_variables'][0]:i for i,g in enumerate(domain['guards']) if g['predicate']['kind']=='retained_scalar'}
    first,second=singles[123],singles[564];need((first,second)==(17,30),'exact two old scalar positions')
    names=deepcopy(raw['variables']);rows=deepcopy(old['residuals'][:1186]);guards=[];vmap={i:i for i in range(1268)};rmap=[[i,i] for i in range(1186)];gmap=[];kept=[]
    for i,g in enumerate(domain['guards']):
        if i==second:gmap.append(dict(old_index=i,new_index=first,kind='replaced_pair_member'));continue
        j=len(guards);aux=list(range(1268+3*j,1271+3*j))
        if i==first:
            label='shared_binomial_digit_product.123.564';names.extend(dict(kind='nonnegative_guard',name=label+'.'+s) for s in ['a','b','c']);a,b,c=aux
            predicate=dict(kind='shared_binomial_digit_product',raw_variables=[123,564],terms=[[1,[123,564]]]);row=dict(label=label,terms=[[1,[123,564]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]);gmap.append(dict(old_index=i,new_index=j,kind='replaced_pair_member'))
        else:
            predicate=deepcopy(g['predicate']);remap=dict(zip(g['auxiliary'],aux))
            for a,b in zip(g['auxiliary'],aux):vmap[a]=b;names.append(deepcopy(old['variables'][a]))
            row=dict(label=old['residuals'][1186+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in old['residuals'][1186+i]['terms']]);rmap.append([1186+i,1186+j]);kept.append(i);gmap.append(dict(old_index=i,new_index=j,kind='retained'))
        guards.append(dict(auxiliary=aux,predicate=predicate));rows.append(row)
    need((len(names),len(rows),len(guards))==(1433,1241,55),'complete new parent dimensions')
    parent=deepcopy(old);parent.update(variant='shared_binomial_digit_product_guard55_raw_literal',variables=names,residuals=rows)
    newdomain=deepcopy(domain);newdomain.update(guards=guards,predicates=55,original_scalar_predicates=45,shared_binomial_digit_product_predicates=1,replaced_scalar_pairs=domain['replaced_scalar_pairs']+[[123,564]],binomial_digit_anchor=[91,537],derived_anchor_source=[94,95])
    radius=deepcopy(load(base/'RADIUS_POLICY.json'));radius['joint_guard']=dict(index=54,predicate=guards[54]['predicate'],auxiliary=guards[54]['auxiliary'])
    cuts=dict(source_row_map=[[i,i] for i in range(1186)],source_variables_unchanged=True,source_rows_unchanged=True,retained_parent_rows=rmap,guard_index_map=gmap,retained_old_guard_indices=kept,replaced_guard_indices=[first,second],retained_old_variable_map=[[i,vmap[i]] for i in sorted(vmap)],removed_old_auxiliary=sorted(set(range(1436))-set(vmap)),new_product_auxiliary=guards[first]['auxiliary'],auxiliary_zero_sets_identified_pointwise=False,raw_coordinate_projection='identity',quantification='For each unrestricted integer tuple satisfying the unchanged1186 body residuals, existence of old56guard witnesses iff existence of new55guard witnesses.')
    certificate=dict(schema='shared_binomial_digit_product_guard_equivalence_v1',body_variables=1268,body_rows=1186,old_parent_variables=1436,old_parent_rows=1242,old_predicates=56,new_parent_variables=1433,new_parent_rows=1241,new_predicates=55,retained_scalars=45,inherited_remainder_products=6,new_product_predicates=1,preserved_replacement_predicates=3,pair=[123,564],anchor=[91,537],derived_anchor=91,direct_anchor_source=[94,95,537],direct_anchor_guard_indices=[singles[v] for v in [94,95,537]],old_guard_indices=[first,second],old_auxiliary_groups=[domain['guards'][i]['auxiliary'] for i in [first,second]],old_guard_rows=[1186+first,1186+second],new_guard_index=first,new_auxiliary=guards[first]['auxiliary'],new_parent_row=1186+first,
        source_identities=dict(derived_anchor=cut([[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]],[83,84,85]),anchor_digit=cut([[1,[530]],[-1,[91]],[-1,[537]],[-1,[]]],[518,519,520]),target_digit=cut([[1,[530]],[-1,[123]],[-1,[564]],[-1,[]]],[540,541,542]),anchored_difference=cut([[1,[123]],[1,[564]],[-1,[91]],[-1,[537]]],[518,519,520],[540,541,542])),
        legendre_graph=dict(polynomial='u-a^2-b^2-c^2-c',auxiliary_domain='all integers',represented_values='all nonnegative integers'),raw_body_byte_unchanged=True,all_power_and_frame_ports_unchanged=True,all_old_signs_restored_before_parent_semantics=True,direct_guard_on_91_assumed=False,denominator_or_pell_meaning_used=False,ordinary_equivalence_proof='PROOF.md',projected_metrics_claimed=False,new_lean_claim=False)
    files={'source/raw_builder.json':(base/'source/raw_builder.json').read_bytes(),'raw/parent.json':encoded(parent),'raw/domain.json':encoded(newdomain),'FRAME_POLICY.json':(base/'FRAME_POLICY.json').read_bytes(),'RADIUS_POLICY.json':encoded(radius),'CUTS.json':encoded(cuts),'CERTIFICATE.json':encoded(certificate)}
    files['BUILD.json']=encoded(dict(generator_sha256=digest(Path(__file__).read_bytes()),source_pins_sha256=digest((HERE/'SOURCE_PINS.json').read_bytes()),files={n:digest(b) for n,b in files.items()},scope='Only complete literal unchanged-body guard materialization and four source-ideal certificates. No optimizer or projected census.'))
    return files
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    for n,b in generate().items():
        f=HERE/n
        if args.check:need(f.is_file() and f.read_bytes()==b,'deterministic whole materialization '+n)
        else:f.parent.mkdir(exist_ok=True,parents=True);f.write_bytes(b)
    print(json.dumps(dict(status='PASS',check=args.check,body_unchanged=True,predicates=55,optimizer_executed=False),sort_keys=True))
if __name__=='__main__':main()
