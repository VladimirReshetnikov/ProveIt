#!/usr/bin/env python3
"""Resolve balanced AX primitive programs for safe diagonal relocations."""
from pathlib import Path
import importlib.util,json,sys,collections
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('source_builder',ROOT.parents[1]/'construction/rebuild.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
def isnode(t):return isinstance(t,tuple) and len(t)==2

def bal(items):
    if len(items)==1:return tuple(items[0]) if isinstance(items[0],list) else items[0]
    k=len(items)//2
    return bal(items[:k]),bal(items[k:])

def grammar(t):
    rules={};known={}
    def rec(t):
        if not isnode(t):return list(t) if isinstance(t,tuple) else t
        if t in known:return known[t]
        kids=[rec(x) for x in t]
        name='s'+str(len(rules));rules[name]=kids;known[t]=name
        return name
    root=rec(t)
    return {'root':root,'rules':rules}

rows=[]
for data in json.loads((ROOT/'transfer_words.json').read_text()):
    name=data['variant']; t=bal(data['node_word'])
    sites,ins=c.source(c.original_nodes(),t)
    sites=[[list(map(int,p)),op,arg] for p,op,arg in sites]
    outcomes=len(ins)+sum(i[0]=='dec' for i in ins)
    count=collections.Counter(i[0] for i in ins)
    result={'variant':name,'primitive_sites':len(sites),'branch_contracts':outcomes,
            'maximum_path':max(len(x[0]) for x in sites),'instruction_counts':dict(count),
            'AX_entry':50,'MP_entry':3693+len(sites)-3812,'shared_return':3799+len(sites)-3812,'Shift_entry':3800+len(sites)-3812,
            'scope':'Resolved source control graph only, no TM allocation or physical runtime certification'}
    (ROOT/(name+'.balanced.grammar.json')).write_text(json.dumps(grammar(t))+'\n')
    (ROOT/(name+'.balanced.instructions.json')).write_text(json.dumps(ins)+'\n')
    (ROOT/(name+'.balanced.sites.json')).write_text(json.dumps(sites)+'\n')
    rows.append(result)
(ROOT/'source_words_receipt.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
