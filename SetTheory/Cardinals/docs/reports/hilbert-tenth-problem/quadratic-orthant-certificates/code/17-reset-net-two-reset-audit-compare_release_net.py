#!/usr/bin/env python3
"""Compare independent and release reset nets by exact renamed incidence.
Checks multiplicities, all source-row arms, metadata, target and symbolic loader.
Writes only its receipt beside this script.
"""
from pathlib import Path
from collections import Counter
import json,hashlib
R=Path(__file__).resolve().parent; RELEASE=R.parent/'two-counter'
read=lambda p:json.loads(p.read_text())
a=read(R/'two_reset_net.json'); b=read(RELEASE/'reset_net.json'); src=read(RELEASE/'source/literal2.json'); declared=read(RELEASE/'net_ledger.json')
rename={}
extra={'counter_1':'A','counter_2':'B','reserve':'reserve','budget':'budget','START':'q:START','CLEAN_2':'q:CLEAN_B','DRAIN':'q:DRAIN','DONE':'q:DONE'}
for p in a['places']:
    rename[p['id']]='q:'+p['label'] if p['kind']=='source_control' else extra[p['label']]
assert len(rename)==len(set(rename.values()))==len(b['places'])==8417
assert set(rename.values())==set(b['places'])
assert set(b['data_places'])=={'A','B','reserve','budget'}
assert set(b['control_places'])==set(b['places'])-set(b['data_places'])
assert set(b['controls'])==set(src['rows'])|{'HALT','START','CLEAN_B','DRAIN','DONE'}
assert {'q:'+q for q in b['controls']}==set(b['control_places'])

def key(pre,post,reset):return (tuple(sorted(pre.items())),tuple(sorted(post.items())),tuple(sorted(reset)))
ka=Counter(key({rename[p]:1 for p in t['input']},{rename[p]:1 for p in t['output']},[rename[p] for p in t['reset']]) for t in a['transitions'])
kb=Counter(key(t['pre'],t['post'],t['reset']) for t in b['transitions'])
assert ka==kb and sum(ka.values())==10756
assert len({t['name'] for t in b['transitions']})==len(b['transitions'])
assert b['semantics']=='enabled if marking >= pre; consume pre, reset listed places to zero, produce post'
by_source={}
for t in b['transitions']:
    assert set(t['pre'])|set(t['post'])|set(t['reset'])<=set(b['places'])
    assert all(w==1 for w in [*t['pre'].values(),*t['post'].values()])
    assert {p:w for p,w in t['pre'].items() if p in b['control_places']}=={'q:'+t['source_control']:1}
    assert {p:w for p,w in t['post'].items() if p in b['control_places']}=={'q:'+t['target_control']:1}
    assert not set(t['reset']) & (set(t['pre'])|set(t['post']))
    by_source.setdefault(t['source_control'],[]).append(t)
for q,(op,i,*ds) in src['rows'].items():
    x=('A','B')[i]; actual=Counter(key(t['pre'],t['post'],t['reset']) for t in by_source[q])
    if op=='ADD':
        want=Counter([key({'q:'+q:1,'reserve':1},{'q:'+ds[0]:1,x:1},[])])
        assert [t['kind'] for t in by_source[q]]==['INC']
    else:
        want=Counter([key({'q:'+q:1,x:1},{'q:'+ds[0]:1,'reserve':1},[]),key({'q:'+q:1},{'q:'+ds[1]:1},[x])])
        assert Counter(t['kind'] for t in by_source[q])=={'SUB_POS':1,'SUB_ZERO':1}
    assert actual==want

# Compare the loaders symbolically before supplementary substitutions.
ini=a['initial_marking']; own={}
assert ini['parameter']=='raw_A'
for p,w in ini['fixed_tokens']:own.setdefault(rename[p],{})['constant']=w
for p,param in ini['parameter_tokens']:own.setdefault(rename[p],{})[param]=1
assert own==b['initial_affine']=={'A':{'raw_A':1},'budget':{'raw_A':1},'q:START':{'constant':1}}
assert b['parameters']==['raw_A']
assert {rename[p]:w for p,w in a['target_marking']}==b['target']=={'q:DONE':1}
for raw in [0,1,64,10**40+7]:
    marking={p:sum(coef*(1 if name=='constant' else raw) for name,coef in b['initial_affine'].get(p,{}).items()) for p in b['places']}
    expected={p:0 for p in b['places']};expected.update({'A':raw,'budget':raw,'q:START':1});assert marking==expected

incidence=Counter()
for t in b['transitions']:
    incidence.update(t['pre']);incidence.update(t['post']);incidence.update(t['reset'])
calc={'places':len(b['places']),'data_places':len(b['data_places']),'control_places':len(b['control_places']),'transitions':len(b['transitions']),'ordinary_input_arcs':sum(len(t['pre']) for t in b['transitions']),'ordinary_output_arcs':sum(len(t['post']) for t in b['transitions']),'reset_arcs':sum(len(t['reset']) for t in b['transitions']),'max_input_weight':max(w for t in b['transitions'] for w in t['pre'].values()),'max_output_weight':max(w for t in b['transitions'] for w in t['post'].values()),'max_ordinary_indegree_transition':max(len(t['pre']) for t in b['transitions']),'max_ordinary_outdegree_transition':max(len(t['post']) for t in b['transitions']),'max_total_incidence_transition':max(len(t['pre'])+len(t['post'])+len(t['reset']) for t in b['transitions']),'max_reset_arcs_per_transition':max(len(t['reset']) for t in b['transitions']),'distinct_reset_places':len({p for t in b['transitions'] for p in t['reset']}),'max_place_incidence':max(incidence.values()),'max_incidence_places':sorted(p for p,v in incidence.items() if v==max(incidence.values())),'transition_kinds':dict(Counter(t['kind'] for t in b['transitions']))}
calc['ordinary_arcs']=calc['ordinary_input_arcs']+calc['ordinary_output_arcs'];calc['all_arcs']=calc['ordinary_arcs']+calc['reset_arcs']
assert calc==declared
receipt={'status':'passed','comparison':'Exact incidence-preserving bijection of all places and multiset of transitions, plus direct source-row arm checks','places_matched':len(rename),'transitions_matched':sum(ka.values()),'source_rows_checked':len(src['rows']),'symbolic_input_loader':'A=raw_A; budget=raw_A; START=1; all other places zero','target':'DONE=1; all other places zero','supplementary_loader_values':[0,1,64,10**40+7],'declared_ledger_exactly_recomputed':calc,'source_paths':['../two-counter/reset_net.json','../two-counter/net_ledger.json','../two-counter/source/literal2.json'],'release_reset_net_sha256':hashlib.sha256((RELEASE/'reset_net.json').read_bytes()).hexdigest()}
(R/'release_comparison_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
