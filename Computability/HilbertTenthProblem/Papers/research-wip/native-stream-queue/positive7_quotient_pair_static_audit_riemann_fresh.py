"""Fresh one-run literal splice audit. Never execute arithmetic source rows."""
from pathlib import Path
import json
import hashlib
from collections import Counter,defaultdict
ROOT=Path('/tmp')
pins={'positive7_guarded_two_form_compiler_root.json':'99e59b73bf1e6a9b0810f8ed862fefe62af00842edafd216e1c0420881ea7784','positive7_quotient_pair_compose_root.json':'eda474bec49c4a2e4fef729c1cae8ed01ee940a8b63a56bb1e1d4cf64684f674'}
data={}
for name,digest in pins.items():
    raw=(ROOT/name).read_bytes();assert hashlib.sha256(raw).hexdigest()==digest;data[name]=json.loads(raw)
old=data['positive7_guarded_two_form_compiler_root.json'];new=data['positive7_quotient_pair_compose_root.json']
def labels(rows):
    c=Counter(row[1] for row in rows);assert set(c)<=set('+-*')
    return dict(M=c['*'],A=c['+']+c['-'],operations=len(rows))
def fixed(name):return {'fixed':name}
results=[]
for graph in new['examples']:
    r=graph['r'];parent=next(g for g in old['examples'] if g['r']==r)
    before=parent['source'];after=graph['source']
    start=next(i for i,row in enumerate(before) if row[0]=='selected_center_8')
    stop=next(i for i,row in enumerate(before) if row[0]=='five_increment_sum_1')
    assert after[:start]==before[:start]
    assert stop-start==30*r and len(after)==len(before)-4*r
    cut=after[start:start+26*r]
    assert labels(before[start:stop])==dict(M=14*r,A=16*r,operations=30*r)
    assert labels(cut)==dict(M=12*r,A=14*r,operations=26*r)
    expected=[];ends=['out_a','out_b','joint_C0','out_d','out_e','out_f'];pair_ports={}
    for j in range(r):
        plus=8+2*j;minus=9+2*j
        # Required six recovery records are matched to parent records directly.
        for s in [plus,minus]:
            for name in [f'selected_center_{s}',f'signed_selected_form_{s}_1',f'signed_selected_form_{s}_2']:
                expected.append(next(row for row in before[start:stop] if row[0]==name))
        for a in [1,2]:
            expected.extend([
              [f'quotient_term_{j}_{a}_1','*',fixed(f'quotient_T_{j}_{a}_1'),f'signed_selected_form_{minus}_1'],
              [f'quotient_term_{j}_{a}_2','*',fixed(f'quotient_T_{j}_{a}_2'),f'signed_selected_form_{minus}_2'],
              [f'quotient_sum_{j}_{a}','+',f'quotient_term_{j}_{a}_1',f'quotient_term_{j}_{a}_2'],
              [f'quotient_difference_{j}_{a}','-',f'signed_selected_form_{plus}_{a}',f'quotient_sum_{j}_{a}'],
            ])
        pair_ports[str(j)]={'plus_slot':plus,'minus_slot':minus,'reduced_forms':[f'quotient_difference_{j}_1',f'quotient_difference_{j}_2']}
        for i in [4,5,6]:
            for a in [1,2]:
                term=f'quotient_action_term_{j}_{i}_{a}';out=f'quotient_action_sum_{j}_{i}_{a}'
                expected.append([term,'*',fixed(f'relator_E_{plus}_{i}_{a}'),f'quotient_difference_{j}_{a}'])
                expected.append([out,'+',ends[i-1],term]);ends[i-1]=out
    assert cut==expected and graph['quotient_pair_ports']==pair_ports
    replacements=dict(zip(parent['ports']['six_increments'],ends))
    assert replacements==graph['parent_suffix_bindings']
    old_suffix=before[stop:];suffix=after[start+26*r:];assert len(old_suffix)==len(suffix)==121
    for original,current in zip(old_suffix,suffix):
        name,op,a,b=original
        assert current==[name,op,replacements.get(a,a) if type(a) is str else a,replacements.get(b,b) if type(b) is str else b]
    assert suffix[33:]==old_suffix[33:] and after[-68:]==before[-68:]
    modified={'source','ports','stages','static_checks','parent_suffix_bindings','certificate_ledger','polynomial_ledger','certificate_prefix_rows'}
    for key,value in parent.items():
        if key not in modified:assert graph[key]==value,(r,key)
    assert graph['ports']==dict(parent['ports'],six_increments=ends)
    for name,c in parent['stages'].items():
        if name=='selected_guarded_relator_appends':assert graph['stages']['selected_quotient_pair_appends']==labels(cut)
        else:assert graph['stages'][name]==c
    assert len(graph['stages'])==len(parent['stages'])
    ranges=[];cursor=0
    for name,c in graph['stages'].items():
        segment=after[cursor:cursor+c['operations']];assert labels(segment)==c
        ranges.append({'stage':name,'first_row':cursor+1,'last_row':cursor+len(segment)});cursor+=len(segment)
    assert cursor==len(after)
    supplied=graph['ordinary_parameters']+graph['positive_auxiliaries'];seen=set(supplied);edge={};cons=defaultdict(list);rolecons=defaultdict(list)
    assert len(seen)==len(supplied)
    for name,op,a,b in after:
        assert name not in seen and op in ['+','-','*']
        for pos,item in enumerate([a,b]):
            if type(item) is str:assert item in seen;cons[item].append([name,pos])
            elif type(item) is dict:assert set(item)=={'fixed'};rolecons[item['fixed']].append([name,pos])
            else:assert type(item) is int
        seen.add(name);edge[name]=[a,b]
    live=set();stack=[graph['output']]
    while stack:
        name=stack.pop()
        if type(name) is str and name not in live:live.add(name);stack.extend(edge.get(name,[]))
    assert set(edge)<=live and set(supplied)<=live
    removed_roles={f'relator_E_{9+2*j}_{i}_{a}' for j in range(r) for i in [4,5,6] for a in [1,2]}
    added_roles={f'quotient_T_{j}_{a}_{b}' for j in range(r) for a in [1,2] for b in [1,2]}
    expected_roles=set(parent['static_checks']['named_fixed_roles'])-removed_roles|added_roles
    assert set(rolecons)==expected_roles and len(rolecons)==6+18*r
    assert graph['static_checks']['named_fixed_roles']==sorted(expected_roles)
    assert all(len(uses)==1 for uses in rolecons.values())
    old_names={row[0] for row in before[start:stop]};new_names={row[0] for row in cut}
    extinct=old_names-new_names
    outside_old=defaultdict(list)
    for row in before[:start]+before[stop:]:
        for pos,x in enumerate(row[2:]):
            if type(x) is str and x in extinct:outside_old[x].append([row[0],pos])
    assert set(outside_old)==set(parent['ports']['six_increments'][3:])
    assert not extinct & set(edge)
    for j in range(r):
        for a in [1,2]:
            assert cons[f'signed_selected_form_{8+2*j}_{a}']==[[f'quotient_difference_{j}_{a}',0]]
            assert cons[f'signed_selected_form_{9+2*j}_{a}']==[[f'quotient_term_{j}_{b}_{a}',1] for b in [1,2]]
            assert cons[f'quotient_difference_{j}_{a}']==[[f'quotient_action_term_{j}_{i}_{a}',1] for i in [4,5,6]]
        for s in [8+2*j,9+2*j]:assert cons[f'selected_center_{s}']==[[f'signed_selected_form_{s}_{a}',1] for a in [1,2]]
    pc=parent['power_cost']
    assert labels(after[:-68])==graph['certificate_ledger']==dict(M=280+40*r+pc,A=550+52*r,operations=830+92*r+pc)
    assert labels(after)==graph['polynomial_ledger']==dict(M=303+40*r+pc,A=595+52*r,operations=898+92*r+pc)
    assert graph['certificate_prefix_rows']==len(after)-68
    splice=graph['splice'];assert splice['old_start_index']==start and splice['old_stop_index']==stop
    assert splice['new_cut_sha256']==hashlib.sha256(json.dumps(cut,separators=(',',':')).encode()).hexdigest()
    assert splice['old_cut_count']==labels(before[start:stop]) and splice['new_cut_count']==labels(cut)
    boundaries=[row[0] for row in cut]+['center_height','center_word','joint_bound','joint_rhs','terminal_product_F_1']
    results.append(dict(r=r,total_rows=len(after),prefix_rows=start,new_cut_rows=len(cut),suffix_rows=len(suffix),stage_ranges=ranges,
      literal_full_coverage=True,all_rows_live=True,all_supplied_live=True,topology=True,certificate=labels(after[:-68]),polynomial=labels(after),witnesses=graph['witnesses'],fixed_roles=len(rolecons),
      prefix_literal_equal=True,finalizer_literal_equal=True,comparisons_literal_equal=True,positive_auxiliaries_literal_equal=True,all_other_interface_fields_literal_equal=True,
      old_removed_cut_external_consumers=dict(outside_old),boundary_consumers={name:cons[name] for name in boundaries},fixed_role_consumers=dict(rolecons),removed_minus_roles=sorted(removed_roles),added_quotient_roles=sorted(added_roles),suffix_bindings=replacements,pair_ports=pair_ports))
assert [g['r'] for g in new['examples']]==[1,2,4]
assert new['r0_fallback']==dict(old['r0_fallback'],inherited_through_guarded_receipt=pins['positive7_guarded_two_form_compiler_root.json'])
result={'status':'PASS','input_pins':pins,'source_arithmetic_evaluated':False,'degree_propagation':False,'saved_helper_replay':False,
 'saved_rows_checked':sum(g['total_rows'] for g in results),'new_cut_rows_checked':sum(g['new_cut_rows'] for g in results),'examples':results,
 'original_checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
out=ROOT/'positive7_quotient_pair_static_audit_riemann_first.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','rows':result['saved_rows_checked'],'new_cut_rows':result['new_cut_rows_checked'],'receipt_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'examples':[{k:g[k] for k in ['r','total_rows','certificate','polynomial','witnesses','fixed_roles']} for g in results]},indent=2))
