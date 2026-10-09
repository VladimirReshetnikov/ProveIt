"""Acyclic simultaneous Tietze elimination on raw word circuits.

This producer is internal: only complete source replay authorizes a verdict.
Images may be arbitrary words, unlike monomial primitive-forest quotients.
"""


def plan_batch(arena, roots, alive, cache=None, *, ordered=False):
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
    graph={};reach={};incoming={};slots=set();selected=[]
    for _,_,slot,g in sorted(candidates):
        arena.tick()
        if g in graph or slot in slots or len(graph)>=len(alive)-1:continue
        deps=supports[slot]-{g};descendants=0
        for parent in deps:
            arena.tick();descendants |= bits[parent] | reach.get(parent,0)
        arena.stats['elimination_cycle_queries']=arena.stats.get('elimination_cycle_queries',0)+1
        if descendants & bits[g]:continue
        # g previously had no outgoing definition. Every new old-vertex path
        # therefore passes through g. Update only its existing ancestors.
        reach[g]=descendants;pending=list(incoming.get(g,()))
        for parent in deps:
            arena.tick();incoming.setdefault(parent,[]).append(g)
        while pending:
            arena.tick();ancestor=pending.pop()
            arena.stats['elimination_reach_visits']=arena.stats.get('elimination_reach_visits',0)+1
            if descendants & ~reach[ancestor]:
                reach[ancestor] |= descendants
                arena.stats['elimination_reach_updates']=arena.stats.get('elimination_reach_updates',0)+1
                pending.extend(incoming.get(ancestor,()))
        graph[g]=deps;slots.add(slot);selected.append(dict(relation=slot,generator=g))
    arena.stats['elimination_batch_attempts']=arena.stats.get('elimination_batch_attempts',0)+1
    if not ordered:return selected
    # Emit a topological witness without changing the selected donors. The
    # checker independently validates this claim from raw source words.
    from collections import deque
    remaining={};followers={g:[] for g in graph}
    for g,deps in graph.items():
        inside=deps&graph.keys();arena.tick(len(inside)+1)
        remaining[g]=len(inside)
        for parent in inside:followers[parent].append(g)
    queue=deque(g for g in graph if not remaining[g]);by_generator={e['generator']:e for e in selected};result=[]
    while queue:
        arena.tick();g=queue.popleft();result.append(by_generator[g])
        for child in followers[g]:
            arena.tick();remaining[child]-=1
            if not remaining[child]:queue.append(child)
    if len(result)!=len(selected):raise ArithmeticError('selected batch contains a cycle')
    return result


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
