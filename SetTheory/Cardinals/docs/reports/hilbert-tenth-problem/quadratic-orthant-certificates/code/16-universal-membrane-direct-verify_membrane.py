#!/usr/bin/env python3
"""Small all-branch tests of the *actual exported* membrane gadgets.
Flat old-object allocation, one structural slot per membrane, then update.
# branches are recorded and stopped because the all-input proof makes # permanent.
This is supplementary finite testing, not the universality proof.
"""
from pathlib import Path
from collections import Counter,defaultdict
from itertools import product
import json
R=Path(__file__).resolve().parent
P=json.loads((R/'virtual3.json').read_text());rows=P['rows']
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

# All-branch single-instruction checks, avoiding self-continuation labels in the
# isolated gadgets so that their continuations can intentionally be made inert.
reps={}
for l,row in rows.items():
    if l not in row[2:]:reps.setdefault((row[0],row[1]),l)
assert len(reps)==6
for (op,reg),l in reps.items():
    relevant={l,l+'$1',l+'$2','b1','b2','b3','d','t','#'}
    rules=[r for r in ALL if r['consume'] in relevant]
    assert not (set(rows[l][2:]) & relevant)
    for inp in product(range(3),repeat=3):
      for pending_t in (0,1):
        children=[(str(i+1),Counter()) for i,n in enumerate(inp) for k in range(n+1)]+[('s',Counter())]
        skin=Counter({l:1});skin.update({'t':pending_t})
        if not skin['t']:del skin['t']
        front={canon(skin,children)};seen=set();terminal=set()
        for depth in range(7):
            nxt=set()
            for cfg in sorted(front):
                if cfg in seen:continue
                seen.add(cfg);stats['trapless_configurations']+=1
                succ,active=successors(cfg,rules)
                if not active:terminal.add(cfg);continue
                for out,emitted in sorted(succ):
                    assert not emitted
                    if trapped(out):stats['trap_outcomes']+=1
                    else:nxt.add(out)
            front=nxt
        assert not(front-seen)
        expected=list(inp)
        if op=='ADD':expected[reg]+=1;cont=rows[l][2]
        elif expected[reg]:expected[reg]-=1;cont=rows[l][2]
        else:cont=rows[l][3]
        assert len(terminal)==1;q=next(iter(terminal));assert q[0]==(cont,)
        assert Counter(h for h,c in q[1])==Counter({**{str(i+1):n+1 for i,n in enumerate(expected)},'s':1})
        assert all(c==() for h,c in q[1]);stats['complete_gadget_cases']+=1

# Full actual accepting membrane run: use every enabled rule from the literal table.
by_symbol=defaultdict(list)
for rule in ALL:by_symbol[rule['consume']].append(rule)
def enabled_symbols(cfg):return set(cfg[0])|{s for h,c in cfg[1] for s in c}
def local_rules(cfg):return [r for s in sorted(enabled_symbols(cfg)) for r in by_symbol[s]]
def compact(cfg,step):
    groups=Counter(cfg[1])
    return {'step':step,'skin':list(cfg[0]),'children':[{'label':h,'objects':list(c),'multiplicity':n} for (h,c),n in sorted(groups.items())]}
regs=[6,0,0];label=P['entry']
initial_children=[(str(i+1),Counter()) for i,n in enumerate(regs) for k in range(n+1)]+[('s',Counter())]
cfg=canon(Counter({label:1}),initial_children);memtrace=[compact(cfg,0)];steps=zeros=cpu=0;maxpop=len(cfg[1])+1;maxobjects=len(cfg[0])
while label!='HALT':
    op,i,*dest=rows[label];zero=op=='SUB' and regs[i]==0
    q=dest[1] if zero else dest[0]
    if op=='ADD':regs[i]+=1
    elif not zero:regs[i]-=1
    for k in range(4 if zero else 3):
        succ,active=successors(cfg,local_rules(cfg));assert active
        good={out for out,emitted in succ if not trapped(out)}
        assert len(good)==1 and all(not em for out,em in succ if not trapped(out))
        cfg=next(iter(good));steps+=1;memtrace.append(compact(cfg,steps))
        maxpop=max(maxpop,len(cfg[1])+1)
        maxobjects=max(maxobjects,len(cfg[0])+sum(len(c) for h,c in cfg[1]))
    expected_skin=Counter({q:1})
    if op=='SUB' and not zero:expected_skin['t']=1
    assert Counter(cfg[0])==expected_skin
    assert Counter(h for h,c in cfg[1])==Counter({**{str(i+1):n+1 for i,n in enumerate(regs)},'s':1})
    assert all(not c for h,c in cfg[1])
    label=q;cpu+=1;zeros+=zero;assert cpu<=328
assert (cpu,steps,zeros,maxpop,maxobjects,regs)==(328,1013,29,30,3,[0,11,0])
_,active=successors(cfg,local_rules(cfg));assert not active and cfg[0]==('HALT',)
# HALT presence alone is not enough: a live trap changes the final state to nonhalting.
trap=canon(Counter({'HALT':1,'#':1}),[(h,Counter(c)) for h,c in cfg[1]])
_,active=successors(trap,local_rules(trap));assert active
stats.update({'complete_register_instructions':cpu,'complete_membrane_steps':steps,'zero_SUB_instructions':zeros,'maximum_population':maxpop,'maximum_objects':maxobjects,'halt_plus_trap_regression':1})
(R/'accepting_membrane_trace.json').write_text(json.dumps({'input':{'L':6,'R':0},'configurations':memtrace,'representation':'Each entry is an exact multiset of elementary child motifs; no membrane identities are encoded.'},indent=2)+'\n')
receipt={'status':'passed','checks':dict(stats),'scope':'324 all-branch small gadget cases, every step of the full accepting run under exact old-object maximality, and a global-halting trap regression. General proof is in PROOF.md.'}
(R/'membrane_verification_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
