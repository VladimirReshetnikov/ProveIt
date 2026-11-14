#!/usr/bin/env python3
"""Independent full source expansion and two independent CFG resolutions.
Checks exact Q-emitter substitution, AX exit push, no-push MP, and H guard tree.
Does not assert a consistency theorem or a proof-assistant endpoint.
"""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verification/reference'))
import source_language as source

def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x

def grammar(path):
    data=json.loads(path.read_text());rules=data['rules']
    def go(x):return tuple(go(y)for y in rules[x])if isinstance(x,str)and x in rules else tup(x)
    return go(data['root'])

def replace(t):
    if t==('leaf','breakTo',1):return 'node49'
    return tuple(map(replace,t))if isinstance(t,tuple)and len(t)==2 else t

def check(machine):
    baseline={k:tup(v)for k,v in json.loads((ROOT/'inputs/primary.nodes.json').read_text()).items()}
    expected=dict(baseline)
    expected['node163']=('node6','node54')
    expected['node170']=(('node36',('node167','node145')),'node57')
    nodes={k:tup(v)for k,v in json.loads((machine/'nodes.json').read_text()).items()}
    assert nodes==expected
    changed=sorted(k for k in nodes if nodes[k]!=baseline[k]);assert changed==['node163','node170']
    g=replace(grammar(ROOT/'inputs/q.grammar.json'))
    assert g==grammar(machine/'grammar.json')==tup(json.loads((machine/'grammar.tree.json').read_text()))
    sites=[];visits={}
    def expand(t,p):
        if isinstance(t,str):
            visits.setdefault(t,[]).append(p)
            return expand(g if t=='x67'else nodes[t],p)
        if t[0]=='leaf':sites.append([p,t[1],t[2]]);return
        assert len(t)==2
        expand(t[0],p+'0');expand(t[1],p+'1')
    expand('node172','')
    assert len(sites)==3671 and sites==json.loads((machine/'sites.json').read_text())
    op={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,op[o],a]for p,o,a in sites]
    by_arithmetic,_=source.graph_arithmetic(mapped);by_intervals=source.graph_intervals(mapped)
    assert by_arithmetic==by_intervals
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[e[0]]]+e[1:]+targets for e,targets in by_arithmetic]
    assert instructions==json.loads((machine/'instructions.json').read_text())
    assert len(visits['x67'])==len(visits['node163'])==1
    # Field-reading and constructor bind AX's fourth argument to the full MP reader.
    assert nodes['node75']==('node74','node65')and nodes['node74']==('node32','node73')
    assert nodes['node164']==('node162','node163')and nodes['node162']==('node75','node37')
    assert nodes['node165']==('node161','node164')and nodes['node161']==(('leaf','dec',3),'x67')
    return {'status':'PASS','source_sites':3671,'source_outcomes':4778,
            'full_tree_expansion_matches':True,'independent_cfg_resolvers_agree':True,
            'changed_source_node_definitions':changed,'Q_grammar_exactly_pinned':True,
            'AX_exit_push_exact':True,'full_MP_field_reader_follows_AX':True,
            'no_other_source_definition_changes':True,
            'scope':'Exact source binding and CFG computation, not a PA or iPRA proof checker.'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,default=ROOT/'machine');p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=check(a.machine);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
