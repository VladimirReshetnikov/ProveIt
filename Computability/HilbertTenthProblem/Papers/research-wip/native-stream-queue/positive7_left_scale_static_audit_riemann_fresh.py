"""Original one-run metadata audit of literal source records, never arithmetic values.
Frozen after first execution. Do not import or replay this file.
"""
import collections
import hashlib
import json
from pathlib import Path

OLD = Path('/tmp/positive7_repeated_pack_compiler_root.json')
NEW = Path('/tmp/positive7_left_scale_compiler_root.json')
OUT = Path('/tmp/positive7_left_scale_static_audit_riemann_first.json')
assert not OUT.exists()
PINS = {OLD:'2fd115c545d412be63b469023b8e13da68648dc79ead5086df2f0aaac6b6377a', NEW:'9a17d38559ae0fc1aac7c987fab827120cdda346fdf2b85fe1b0eb9b1b523d4a'}
data = {}
for p, expected in PINS.items():
    raw = p.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == expected
    data[p] = json.loads(raw)
old, new = data[OLD], data[NEW]

def tally(rows):
    labels = collections.Counter(a[1] for a in rows)
    assert set(labels) <= {'+','-','*'}
    return dict(M=labels['*'], A=labels['+']+labels['-'], operations=len(rows))

def fingerprint(records):
    return hashlib.sha256(json.dumps(records,separators=(',',':')).encode()).hexdigest()

def partition(graph):
    answer, at = {}, 0
    for name, expected in graph['stages'].items():
        answer[name] = graph['source'][at:at+expected['operations']]
        assert tally(answer[name]) == expected
        at += expected['operations']
    assert at == len(graph['source'])
    return answer

def uses(rows):
    found = collections.defaultdict(list)
    for name, op, a, b in rows:
        for position, v in enumerate([a,b],start=2):
            if isinstance(v,str): found[v].append([name,position])
    return dict(found)

assert new['fixed_data_recipe'] == old['fixed_data_recipe']
assert new['r0_fallback'] == old['r0_fallback']
assert len(new['examples']) == len(old['examples']) == 3
results=[]
for parent, child in zip(old['examples'],new['examples']):
    r,m,ell = parent['r'],parent['m'],parent['ell']
    assert child['r']==r and m==8+2*r and ell==62+6*r
    groups, actual = partition(parent), partition(child)
    P,Pm = parent['ports']['P'],parent['ports']['selector_power']
    D,S = parent['ports']['D'],parent['ports']['S']
    before={a[0]:a for a in parent['source']}
    after={a[0]:a for a in child['source']}
    assert len(before)==len(parent['source']) and len(after)==len(child['source'])

    # Bind the old left cut literally to its declared lane grammar.
    old_left,word=[],D
    assert parent['lanes_in_order'][-1][0]==D
    for i in range(ell-2,m-1,-1):
        mul,add='left_shift_'+str(i),'left_join_'+str(i)
        old_left += [[mul,'*',word,P],[add,'+',mul,parent['lanes_in_order'][i][0]]]
        word=add
    old_left_exit=word
    assert old_left==[a for a in groups['two_upper_horner_packs'] if a[0].startswith('left_')]
    assert tally(old_left)==dict(M=53+4*r,A=53+4*r,operations=106+8*r)
    high_output=[a for a in groups['two_upper_horner_packs'] if a[0].startswith('output_')]
    assert len(old_left)+len(high_output)==len(groups['two_upper_horner_packs'])
    assert tally(high_output)==dict(M=52+4*r,A=52+4*r,operations=104+8*r)
    old_power=groups['fixed_native_power_after_shared_square']
    pc=parent['power_cost']
    assert tally(old_power)==dict(M=pc-1,A=0,operations=pc-1)
    assert 'scale_square_0' not in {a[0] for a in old_power}

    # Fresh expected schedule from the fully paid mathematical identities.
    replacement=[
        ['left_support_P4','*','scale_square_0','scale_square_0'],
        ['left_support_P5','*','scale_square_0','pack_P3'],
        ['left_support_P12','*','pack_P6','pack_P6'],
        ['left_support_P14','*','pack_P7','pack_P7'],
        ['left_support_P28','*','left_support_P14','left_support_P14'],
        ['left_pair_factor_2','+',1,'scale_square_0'],
        ['left_pair_factor_6','+',1,'pack_P6'],
        ['left_pair_factor_7','+',1,'pack_P7'],
        ['left_pair_factor_14','+',1,'left_support_P14'],
        ['left_four_seven_factor','*','left_pair_factor_7','left_pair_factor_14'],
    ]
    history='H_7'
    for i in range(6,0,-1):
        mul,add='left_history_shift_'+str(i),'left_history_join_'+str(i)
        replacement += [[mul,'*',history,P],[add,'+',mul,'H_'+str(i)]]
        history=add
    replacement += [
        ['left_short_history_difference','-','left_history_join_6','H_7'],
        ['left_short_history_correction','*','left_support_P5','left_short_history_difference'],
        ['left_short_history_b','-','left_history_join_1','left_short_history_correction'],
        ['left_high_tail_shift','*',D,P],
        ['left_high_tail','+','left_high_tail_shift',S],
    ]
    high='left_high_tail'
    for j in reversed(range(r)):
        f1,f2=parent['centered_input_forms'][str(j)]
        small,pair,repeat,shift,join=[stem+str(j) for stem in ['left_form_shift_','left_form_pair_','left_form_repeated_','left_form_high_shift_','left_form_high_join_']]
        replacement += [[small,'*',P,f2],[pair,'+',small,f1],[repeat,'*','left_pair_factor_2',pair],[shift,'*','left_support_P4',high],[join,'+',shift,repeat]]
        high=join
    replacement += [['left_seven_repeated','*','left_four_seven_factor','left_history_join_1'],['left_seven_high_shift','*','left_support_P28',high],['left_seven_high_join','+','left_seven_high_shift','left_seven_repeated']]
    high='left_seven_high_join'
    for label,block in [('b','left_short_history_b'),('a','left_history_join_2')]:
        repeat,shift,join='left_six_repeated_'+label,'left_six_high_shift_'+label,'left_six_high_join_'+label
        replacement += [[repeat,'*','left_pair_factor_6',block],[shift,'*','left_support_P12',high],[join,'+',shift,repeat]]
        high=join
    assert high=='left_six_high_join_a'
    assert tally(replacement)==dict(M=20+3*r,A=16+2*r,operations=36+5*r)
    power=[
        ['native_shared_P19','*','left_support_P12','pack_P7'],
        ['native_shared_m_plus_19','*',Pm,'native_shared_P19'],
        ['native_shared_double','*','native_shared_m_plus_19','native_shared_m_plus_19'],
        ['native_shared_scale','*',Pm,'native_shared_double'],
    ]
    expected={}
    prefix_names=list(groups)[:list(groups).index('two_upper_horner_packs')]
    for label in prefix_names:expected[label]=groups[label]
    expected['repeated_high_left_pack']=replacement
    expected['upper_output_horner_pack']=high_output
    bindings={old_left_exit:high,parent['ports']['T']:'native_shared_scale'}
    def bound(rows):
        return [[a[0],a[1],*[bindings.get(v,v) if isinstance(v,str) else v for v in a[2:]]] for a in rows]
    expected['factored_pack_joins']=bound(groups['factored_pack_joins'])
    expected['shared_native_scale']=power
    expected['complete_native64']=bound(groups['complete_native64'])
    for label in list(groups)[list(groups).index('complete_native64')+1:]:expected[label]=groups[label]
    assert list(expected)==list(actual)
    assert all(expected[k]==actual[k] for k in expected)
    all_expected=[a for part in expected.values() for a in part]
    assert all_expected==child['source']

    removed=old_left+old_power
    removed_names={a[0] for a in removed}
    assert not removed_names.intersection(after)
    old_uses,new_uses=uses(parent['source']),uses(child['source'])
    boundary={n:[use for use in old_uses.get(n,[]) if use[0] not in removed_names] for n in removed_names}
    boundary={n:v for n,v in boundary.items() if v}
    assert boundary=={old_left_exit:[['left_selector_shift',2]],parent['ports']['T']:[['pell_q',3]]}
    assert all(n not in new_uses for n in removed_names)
    rewritten=[{'before':before[a[0]],'after':a} for a in child['source'] if a[0] in before and a!=before[a[0]]]
    assert [a['after'][0] for a in rewritten]==['left_selector_shift','pell_q']
    kept=[a[0] for a in child['source'] if a[0] in before and a==before[a[0]]]
    novel=[a for a in child['source'] if a[0] not in before]
    assert novel==replacement+power
    assert len(parent['source'])==len(kept)+len(removed)+2
    assert len(child['source'])==len(kept)+len(novel)+2
    assert after['scale_square_0']==before['scale_square_0']==['scale_square_0','*',P,P]
    assert new_uses['left_support_P12']==[['left_six_high_shift_b',2],['left_six_high_shift_a',2],['native_shared_P19',2]]
    assert new_uses['left_history_join_6']==[['left_history_shift_5',2],['left_short_history_difference',2]]
    assert new_uses['left_history_join_2']==[['left_history_shift_1',2],['left_six_repeated_a',3]]
    assert new_uses[high]==[['left_selector_shift',2]]
    assert new_uses['native_shared_scale']==[['pell_q',3]]
    assert new_uses[Pm]==old_uses[Pm]+[['native_shared_m_plus_19',2],['native_shared_scale',2]]
    for n in parent['ports']['native_packs']:
        assert after[n]==before[n]

    altered={'source','stages','ports','power_cost','pack_splice','static_checks','polynomial_ledger','certificate_ledger','certificate_prefix_rows'}
    for key in set(parent)-altered:assert child[key]==parent[key],(r,key)
    assert set(parent)-set(child)=={'power_cost','pack_splice'}
    assert set(child)-set(parent)=={'native_scale_products','parent_binary_power_cost','left_scale_splice'}
    assert child['ports']==dict(parent['ports'],T='native_shared_scale',high_left_pack=high,left_support_P12='left_support_P12')
    assert child['native_scale_products']==4 and child['parent_binary_power_cost']==pc
    witness=child['left_scale_splice']
    assert witness['removed_rows']==removed and witness['removed_digest']==fingerprint(removed)
    assert witness['literal_retained_row_names']==kept and witness['rebound_rows']==rewritten
    assert witness['old_source_digest']==fingerprint(parent['source']) and witness['new_source_digest']==fingerprint(child['source'])
    assert witness['new_left_exit']==high and witness['new_scale_exit']=='native_shared_scale'
    assert witness['new_left_ledger']==tally(replacement) and witness['native_scale_ledger']==dict(M=4,A=0,operations=4)
    assert witness['finalizer_literal_equal'] and witness['comparisons_literal_equal'] and witness['positive_auxiliaries_literal_equal']

    supplied=['x']+child['positive_auxiliaries']
    known=set(supplied);deps={};roles=collections.Counter()
    assert len(known)==len(supplied)
    for name,op,a,b in child['source']:
        assert name not in known and op in ('+','-','*')
        for value in [a,b]:
            if isinstance(value,str):assert value in known
            elif isinstance(value,dict):
                assert set(value)=={'fixed'} and isinstance(value['fixed'],str)
                roles[value['fixed']]+=1
            else:assert type(value) is int
        known.add(name);deps[name]=[x for x in [a,b] if isinstance(x,str)]
    live=set();pending=[child['output']]
    while pending:
        node=pending.pop()
        if node not in live:live.add(node);pending.extend(deps.get(node,[]))
    assert set(deps)<=live and set(supplied)<=live
    assert sorted(roles)==parent['static_checks']['named_fixed_roles']==child['static_checks']['named_fixed_roles']
    assert len(roles)==6+18*r and set(roles.values())=={1}
    assert child['static_checks']['topology'] and child['static_checks']['all_computed_live'] and child['static_checks']['all_supplied_live']
    assert child['equations']==len(child['comparisons'])==23
    assert child['witnesses']==len(supplied)-1==96+6*r
    assert child['source'][-68:]==parent['source'][-68:]
    assert tally(child['source'][-68:])==dict(M=23,A=45,operations=68)
    gm,ga=parent['geometric_extension']['M'],parent['geometric_extension']['A']
    poly,cert=tally(child['source']),tally(child['source'][:-68])
    assert poly==child['polynomial_ledger']==dict(M=224+33*r+gm,A=504+44*r+ga,operations=728+77*r+gm+ga)
    assert cert==child['certificate_ledger']==dict(M=201+33*r+gm,A=459+44*r+ga,operations=660+77*r+gm+ga)
    assert child['certificate_prefix_rows']==len(child['source'])-68
    assert len(removed)==105+8*r+pc and len(novel)==40+5*r
    results.append({'r':r,'parent_rows':len(parent['source']),'rows':len(child['source']),'coverage':{'literal':len(kept),'new':len(novel),'rebound':2},'removed_rows':len(removed),'deleted_boundary':boundary,'rebound_records':rewritten,'left_rows_and_ledger':tally(replacement),'native_rows_and_ledger':tally(power),'polynomial':poly,'certificate':cert,'witnesses':child['witnesses'],'fixed_roles_with_consumer_counts':dict(sorted(roles.items())),'full_source_digest':fingerprint(all_expected),'complete_stage_census':child['stages'],'critical_consumer_lists':{n:new_uses[n] for n in ['scale_square_0',Pm,'left_support_P12','left_history_join_6','left_history_join_2',high,'native_shared_scale']},'all_unchanged_fields_literal':True,'topology_and_full_liveness':True,'same_lanes_and_semantic_descriptors':True})

assert [a['r'] for a in results]==[1,2,4]
assert sum(a['rows'] for a in results)==2743
result={'status':'PASS','input_pins':{str(p):v for p,v in PINS.items()},'saved_rows_checked':2743,'parent_rows_checked':2983,'source_arithmetic_evaluated':False,'degree_propagation':False,'saved_helper_replay':False,'examples':results,'original_checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','saved_rows_checked':2743,'coverage':{key:sum(a['coverage'][key] for a in results) for key in ['literal','new','rebound']},'examples':[{'r':a['r'],'rows':a['rows'],'coverage':a['coverage'],'poly':a['polynomial']} for a in results]},indent=2))
