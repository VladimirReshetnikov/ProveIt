#!/usr/bin/env python3
"""Literal unit-weight reset net. All files generated locally; stdlib only."""
from pathlib import Path
from collections import Counter
import json, hashlib
ROOT=Path(__file__).resolve().parent

def compile_net(program,*,initial_affine=None,parameters=None):
    regs=program['registers']; rows=program['rows']; ctrl=list(rows)+[program['halt'],'START']+['CLEAN_'+p for p in regs[1:]]+['DRAIN','DONE']
    cp=lambda x:'q:'+x
    data=regs+['reserve','budget']; places=data+[cp(x) for x in ctrl]; transitions=[]
    if len(set(places))!=len(places):raise ValueError('Source identifiers collide with reserved control or resource names; rename them first')
    assert program['entry'] in rows or program['entry']==program['halt']
    assert all(dst in rows or dst==program['halt'] for row in rows.values() for dst in row[2:])
    def add(name,src,dst,pre=None,post=None,reset=(),kind=None):
        a={cp(src):1};b={cp(dst):1}
        for p,n in (pre or {}).items():a[p]=a.get(p,0)+n
        for p,n in (post or {}).items():b[p]=b.get(p,0)+n
        transitions.append({'name':name,'pre':a,'post':b,'reset':list(reset),'source_control':src,'target_control':dst,'kind':kind or name})
    add('pump','START','START',post={'reserve':1,'budget':1})
    add('enter','START',program['entry'])
    for label,row in rows.items():
        op,r,*dst=row;p=regs[r]
        if op=='ADD':add(label+':inc',label,dst[0],{'reserve':1},{p:1},kind='INC')
        else:
            assert op=='SUB'
            add(label+':pos',label,dst[0],{p:1},{'reserve':1},kind='SUB_POS')
            add(label+':zero',label,dst[1],reset=[p],kind='SUB_ZERO')
    phases=[program['halt']]+['CLEAN_'+p for p in regs[1:]]+['DRAIN']
    for i,p in enumerate(regs):
        add('clean_'+p,phases[i],phases[i],{p:1},{'reserve':1},kind='CLEAN')
        add('advance_'+p,phases[i],phases[i+1],kind='ADVANCE')
    add('drain','DRAIN','DRAIN',{'reserve':1,'budget':1})
    add('finish','DRAIN','DONE')
    if initial_affine is None:
        if regs!=['L','R','T']:raise ValueError('Supply an explicit affine input map for a different register interface')
        initial_affine={'L':{'L':1},'R':{'R':1},'budget':{'L':1,'R':1},'q:START':{'constant':1}}
    if parameters is None:parameters=list(dict.fromkeys(k for v in initial_affine.values() for k in v if k!='constant'))
    assert set(initial_affine)<=set(places)
    assert all(set(v)<=set(parameters)|{'constant'} and all(type(n) is int and n>=0 for n in v.values()) for v in initial_affine.values())
    return {'format':'unit-reset-net-v1','semantics':'enabled if marking >= pre; consume pre, reset listed places to zero, produce post',
        'places':places,'data_places':data,'control_places':[cp(x) for x in ctrl],'controls':ctrl,
        'transitions':transitions,'initial_affine':initial_affine,
        'parameters':parameters,'target':{'q:DONE':1}}

def initial(net,L,R):
    """The default three-counter affine input helper; other interfaces supply their own map."""
    assert net['data_places'][:3]==['L','R','T']
    if type(L) is not int or L<0 or type(R) is not int or R<0:
        raise ValueError('Initial counters must be exact nonnegative integers')
    return {'L':L,'R':R,'budget':L+R,'q:START':1}

def fire(net,marking,transition):
    if type(marking) is not dict:
        raise ValueError('A marking must be a dictionary')
    places=set(net['places'])
    if any(type(p) is not str or p not in places or type(n) is not int or n<0 for p,n in marking.items()):
        raise ValueError('A marking must use known places and exact nonnegative integers')
    t=net['transitions'][transition] if type(transition) is int else transition
    if any(marking.get(p,0)<n for p,n in t['pre'].items()):raise ValueError('transition disabled: '+t['name'])
    out={p:marking.get(p,0)-t['pre'].get(p,0) for p in net['places']}
    loss=sum(out[p] for p in t['reset'])
    for p in t['reset']:out[p]=0
    for p,n in t['post'].items():out[p]+=n
    return {p:n for p,n in out.items() if n},loss

def ledger(net):
    ts=net['transitions'];inc=Counter()
    for t in ts:
        for p in t['pre']:inc[p]+=1
        for p in t['post']:inc[p]+=1
        for p in t['reset']:inc[p]+=1
    return {'places':len(net['places']),'data_places':len(net['data_places']),'control_places':len(net['control_places']),
      'transitions':len(ts),'ordinary_input_arcs':sum(len(t['pre']) for t in ts),
      'ordinary_output_arcs':sum(len(t['post']) for t in ts),
      'ordinary_arcs':sum(len(t['pre'])+len(t['post']) for t in ts),'reset_arcs':sum(len(t['reset']) for t in ts),
      'all_arcs':sum(len(t['pre'])+len(t['post'])+len(t['reset']) for t in ts),
      'max_input_weight':max(n for t in ts for n in t['pre'].values()),
      'max_output_weight':max(n for t in ts for n in t['post'].values()),
      'max_ordinary_indegree_transition':max(len(t['pre']) for t in ts),
      'max_ordinary_outdegree_transition':max(len(t['post']) for t in ts),
      'max_total_incidence_transition':max(len(t['pre'])+len(t['post'])+len(t['reset']) for t in ts),
      'max_reset_arcs_per_transition':max(len(t['reset']) for t in ts),'distinct_reset_places':len({p for t in ts for p in t['reset']}),
      'max_place_incidence':max(inc.values()),'max_incidence_places':[p for p,v in inc.items() if v==max(inc.values())],
      'transition_kinds':dict(Counter(t['kind'] for t in ts))}

def main():
    program=json.loads((ROOT/'source/virtual3.json').read_text());net=compile_net(program)
    (ROOT/'reset_net.json').write_text(json.dumps(net,indent=2)+'\n')
    (ROOT/'net_ledger.json').write_text(json.dumps(ledger(net),indent=2)+'\n')
    print(json.dumps(ledger(net),indent=2))
if __name__=='__main__':main()
