#!/usr/bin/env python3
"""Small all-branch tests of the *actual exported* membrane gadgets.
Flat old-object allocation, one structural slot per membrane, then update.
# branches are recorded and stopped because the all-input proof makes # permanent.
This is supplementary finite testing, not the universality proof.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import json
R=Path(__file__).resolve().parent
P=json.loads((R/'literal2.json').read_text());rows=P['rows']
ALL=[json.loads(z) for z in (R/'membrane_rules.jsonl').read_text().splitlines()]
stats=Counter()

def canon(skin,children):
    return tuple(sorted(skin.elements())),tuple(sorted((h,tuple(sorted(c.elements()))) for h,c in children))
def trapped(cfg):return '#' in cfg[0] or any('#' in c for h,c in cfg[1])
def successors(cfg,rules):
    """Enumerate all assignments to distinct old object occurrences.
    Each action is (rule, target membrane); an incoming action consumes a skin token.
    Multiple identical schedules are quotient-deduplicated only after exact allocation.
    """
    regs=[Counter(cfg[0])]+[Counter(c) for h,c in cfg[1]]
    labels=['skin']+[h for h,c in cfg[1]]
    tokens=[(loc,s) for loc,c in enumerate(regs) for s,n in c.items() for _ in range(n)]
    choices=[]
    for loc,s in tokens:
        opts=[]
        for i,r in enumerate(rules):
            if r['consume']!=s:continue
            if r['kind']=='in':
                if loc==0:
                    opts += [(i,k) for k in range(1,len(regs)) if labels[k]==r['label']]
            elif r['label']==labels[loc]:opts.append((i,loc))
        choices.append([None]+opts)
    outputs=set();activity=False
    for acts in product(*choices):
        busy=set();legal=True
        for action in acts:
            if action is None:continue
            i,k=action
            if rules[i]['kind']!='evolve':
                if k in busy:legal=False;break
                busy.add(k)
        if not legal:continue
        # Inclusion maximality: any still-available action on an unused token?
        for opts,chosen in zip(choices,acts):
            if chosen is None and any(rules[i]['kind']=='evolve' or k not in busy for i,k in opts[1:]):
                legal=False;break
        if not legal:continue
        active=any(a is not None for a in acts);activity|=active
        new=[c.copy() for c in regs];modes={};up=Counter()
        for (loc,s),action in zip(tokens,acts):
            if action is None:continue
            i,k=action;r=rules[i];new[loc][s]-=1
            if not new[loc][s]:del new[loc][s]
            if r['kind']=='evolve':new[loc].update(dict(r['produce']))
            elif r['kind']=='in':new[k].update(dict(r['produce']))
            else:modes[k]=r
        children=[]
        for k in range(1,len(regs)):
            r=modes.get(k);h=labels[k];c=new[k]
            if r is None:children.append((h,c))
            elif r['kind']=='out':new[0].update(dict(r['produce']));children.append((h,c))
            elif r['kind']=='dissolve':new[0].update(c);new[0].update(dict(r['produce']))
            elif r['kind']=='divide':
                for field in ('produce','other'):
                    cc=c.copy();cc.update(dict(r[field]));children.append((h,cc))
            else:raise AssertionError(r)
        if 0 in modes:
            assert modes[0]['kind']=='out'
            up.update(dict(modes[0]['produce']))
        out=canon(new[0],children)
        outputs.add((out,tuple(sorted(up.elements()))))
        stats['maximal_allocations']+=1
    return outputs,activity

# Fix representative rows of all four operation/register shapes.
reps={}
for l,row in rows.items():reps.setdefault((row[0],row[1]),l)
for (op,reg),l in reps.items():
    relevant={l,l+'$1',l+'$2','b1','b2','d','t','#'}
    rules=[r for r in ALL if r['consume'] in relevant]
    targets=set(rows[l][2:]);assert not (targets & relevant)
    for n1 in range(4):
     for n2 in range(4):
      for pending_t in (0,1):
        inp=[n1,n2];children=[('1',Counter())]*(n1+1)+[('2',Counter())]*(n2+1)+[('s',Counter())]
        skin=Counter({l:1});skin.update({'t':pending_t})
        if not skin['t']:del skin['t']
        initial=canon(skin,children);front={initial};seen=set();terminal=set()
        for depth in range(7):
            nxt=set()
            for cfg in sorted(front):
                if cfg in seen:continue
                seen.add(cfg);stats['trapless_configurations']+=1
                stats['maximum_trapless_depth']=max(stats['maximum_trapless_depth'],depth)
                succ,active=successors(cfg,rules)
                if not active:terminal.add(cfg);continue
                for out,emitted in sorted(succ):
                    assert not emitted,(op,reg,cfg,out,emitted)
                    if trapped(out):stats['trap_outcomes']+=1
                    else:nxt.add(out)
            front=nxt
        assert not (front-seen),(l,inp,front-seen)
        expected=inp.copy()
        if op=='ADD':expected[reg]+=1;cont=rows[l][2]
        elif expected[reg]:expected[reg]-=1;cont=rows[l][2]
        else:cont=rows[l][3]
        assert len(terminal)==1,(l,inp,terminal)
        q=next(iter(terminal));assert q[0]==(cont,),q
        assert Counter(h for h,c in q[1])==Counter({'1':expected[0]+1,'2':expected[1]+1,'s':1})
        assert all(c==() for h,c in q[1])
        stats['complete_gadget_cases']+=1

# Explicit regression: wrong phase2 choice can reach an inert continuation with #.
l=reps[('SUB',0)];rel={l,l+'$1',l+'$2','b1','b2','d','t','#'}
rules=[r for r in ALL if r['consume'] in rel]
start=canon(Counter({l:1}),[('1',Counter()),('2',Counter()),('s',Counter())])
front={start};witness=None
for depth in range(6):
    nxt=set()
    for cfg in sorted(front):
        succ,active=successors(cfg,rules)
        for out,emitted in sorted(succ):
            if trapped(out) and any(q in out[0] for q in rows[l][2:]):
                witness=out
                # The inert continuation does not make this configuration halt.
                _,active2=successors(out,rules);assert active2
                break
            nxt.add(out)
        if witness:break
    if witness:break
    front=nxt
assert witness is not None
stats['halt_control_with_live_trap_regressions']=1
receipt={'status':'passed','checks':dict(stats),'scope':'All maximal branches on small ADD/SUB gadgets extracted from literal export; global proof in PROOF.md covers arbitrary counter values and all runs.'}
(R/'membrane_verification_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
