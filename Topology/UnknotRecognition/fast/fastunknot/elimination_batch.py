"""Acyclic simultaneous Tietze elimination on raw word circuits.

This producer is internal: only complete source replay authorizes a verdict.
Images may be arbitrary words, unlike monomial primitive-forest quotients.
"""


def plan_batch(arena, roots, alive, cache=None):
    if cache is None:cache={}
    labels=cache.setdefault('labels',sorted(alive))
    bits=cache.setdefault('bits',{g:1<<i for i,g in enumerate(labels)})
    memo=cache.setdefault('masks',{0:(0,0)})
    for root in roots:
        pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in memo:continue
            rule=arena.rules[node]
            if rule[0]=='t':memo[node]=(bits[abs(rule[1])],0)
            elif not ready:pending.extend(((node,True),(rule[2],False),(rule[1],False)));continue
            else:
                p,a=memo[rule[1]];q,b=memo[rule[2]]
                memo[node]=(p|q,a|b|(p&q))
    counts,_=arena.summarize(roots);candidates=[];supports={}
    for slot,root in enumerate(roots):
        arena.tick();present,repeated=memo[root];single=present&~repeated
        support=set()
        while present:
            arena.tick();bit=present&-present;support.add(labels[bit.bit_length()-1]);present^=bit
        supports[slot]=support
        while single:
            arena.tick();bit=single&-single;g=labels[bit.bit_length()-1];single^=bit
            if g in alive and support<=alive:
                length=arena.lengths[root];candidates.append(((length-2)*counts[g],length,slot,g))
    graph={};slots=set();selected=[]
    for _,_,slot,g in sorted(candidates):
        arena.tick()
        if g in graph or slot in slots or len(graph)>=len(alive)-1:continue
        deps=supports[slot]-{g};pending=list(deps);seen=set();cycle=False
        while pending:
            arena.tick();v=pending.pop()
            if v==g:cycle=True;break
            if v in seen:continue
            seen.add(v);pending.extend(graph.get(v,()))
        if cycle:continue
        graph[g]=deps;slots.add(slot);selected.append(dict(relation=slot,generator=g))
    arena.stats['elimination_batch_attempts']=arena.stats.get('elimination_batch_attempts',0)+1
    return selected


def apply_batch(arena, roots, alive, selected):
    """Apply internally checked singleton donors with acyclic dependencies."""
    replacements={};slots=set()
    for entry in selected:
        arena.tick();slot,g=entry['relation'],entry['generator'];root=roots[slot]
        count,position,signed=arena.occurrence(root,g)
        if count!=1:raise ArithmeticError('batch donor is not a singleton')
        rest=arena.concat(arena.slice(root,position+1,arena.lengths[root]),arena.slice(root,0,position))
        value=arena.inverse(rest) if signed>0 else rest
        replacements[g]=value;replacements[-g]=arena.inverse(value);slots.add(slot)
    # Link eliminated terminals to their source-word definitions. The donor
    # dependency DAG makes this enlarged word circuit acyclic, even though
    # links can point forward in arena allocation order.
    mapped={0:0}
    for slot,root in enumerate(roots):
        if slot in slots:continue
        pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in mapped:continue
            rule=arena.rules[node]
            if rule[0]=='t':
                target=replacements.get(rule[1])
                if target is None:mapped[node]=node
                elif ready:mapped[node]=mapped[target]
                else:pending.extend(((node,True),(target,False)))
            elif ready:mapped[node]=arena.concat(mapped[rule[1]],mapped[rule[2]])
            else:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
    roots[:]=[0 if slot in slots else mapped[root] for slot,root in enumerate(roots)]
    alive.difference_update(entry['generator'] for entry in selected)
    arena.stats['elimination_batch_rounds']=arena.stats.get('elimination_batch_rounds',0)+1
    arena.stats['elimination_batch_generators']=arena.stats.get('elimination_batch_generators',0)+len(selected)
