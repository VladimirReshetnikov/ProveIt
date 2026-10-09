"""Independent source-replay checks for acyclic singleton elimination.

No producer planning, metadata or substitution routine is imported.
"""
from collections import deque


def _entries(move, count, alive, tick):
    tick()
    if type(move) is not dict or set(move)!={'kind','entries'} or move['kind']!='elimination_batch':return None
    entries=move['entries']
    if type(entries) is not list or not entries or len(entries)>=len(alive):return None
    children=set();slots=set()
    for entry in entries:
        tick()
        if type(entry) is not dict or set(entry)!={'relation','generator'}:return None
        slot,g=entry['relation'],entry['generator']
        if (type(slot) is not int or not 0<=slot<count or slot in slots
                or type(g) is not int or g not in alive or g in children):return None
        slots.add(slot);children.add(g)
    return children,slots


def _order(dependencies, tick):
    remaining={};followers={g:[] for g in dependencies}
    for g,deps in dependencies.items():
        tick(len(deps)+1);inside=deps&dependencies.keys();remaining[g]=len(inside)
        for parent in inside:followers[parent].append(g)
    queue=deque(g for g,n in remaining.items() if n==0);order=[]
    while queue:
        tick();g=queue.popleft();order.append(g)
        for child in followers[g]:
            tick();remaining[child]-=1
            if remaining[child]==0:queue.append(child)
    return order if len(order)==len(dependencies) else None


def replay_compressed_batch(arena, roots, alive, move):
    parsed=_entries(move,len(roots),alive,arena.tick)
    if parsed is None:return False
    children,slots=parsed;dependencies={};images={}
    # Derive occurrence counts and support together without the producer's
    # singleton masks. No state roots or live labels change during validation.
    for entry in move['entries']:
        arena.tick();slot,g=entry['relation'],entry['generator'];root=roots[slot]
        count,position,signed=arena.occurrence(root,g)
        if count!=1:return False
        support=set()
        for node in arena._reachable([root]):
            arena.tick();rule=arena.rules[node]
            if rule[0]=='t':support.add(abs(rule[1]))
        if not support<=alive:return False
        dependencies[g]=support-{g}
        prefix=arena.slice(root,0,position);suffix=arena.slice(root,position+1,arena.lengths[root])
        rest=arena.concat(suffix,prefix)
        images[g]=arena.inverse(rest) if signed>0 else rest
        images[-g]=arena.inverse(images[g])
    if _order(dependencies,arena.tick) is None:return False
    # Independent Kahn evaluation of the linked source grammar, instead of
    # the producer's recursive postorder substitution.
    needed=arena._reachable([r for i,r in enumerate(roots) if i not in slots]+list(images.values()))
    incoming={};followers={node:[] for node in needed};sources={}
    for node in needed:
        arena.tick();rule=arena.rules[node]
        source=(images[rule[1]],) if rule[0]=='t' and rule[1] in images else rule[1:] if rule[0]=='c' else ()
        sources[node]=source;deps=set(source)-{0};incoming[node]=len(deps)
        for dep in deps:followers[dep].append(node)
    queue=deque(node for node,n in incoming.items() if n==0);mapped={0:0}
    while queue:
        arena.tick();node=queue.popleft();rule=arena.rules[node];source=sources[node]
        if rule[0]=='c':mapped[node]=arena.concat(mapped[source[0]],mapped[source[1]])
        elif source:mapped[node]=mapped[source[0]]
        else:mapped[node]=node
        for user in followers[node]:
            arena.tick();incoming[user]-=1
            if incoming[user]==0:queue.append(user)
    if len(mapped)!=len(needed)+1:return False
    roots[:]=[0 if i in slots else mapped[root] for i,root in enumerate(roots)]
    alive.difference_update(children)
    return True


def replay_literal_batch(words, alive, move, budget):
    parsed=_entries(move,len(words),alive,budget.tick)
    if parsed is None:return False
    children,slots=parsed;dependencies={};definitions={}
    for entry in move['entries']:
        g=entry['generator'];word=words[entry['relation']];budget.tick(len(word)+1)
        positions=[i for i,x in enumerate(word) if abs(x)==g]
        support={abs(x) for x in word}
        if len(positions)!=1 or not support<=alive:return False
        i=positions[0];rest=word[i+1:]+word[:i]
        definitions[g]=[-x for x in reversed(rest)] if word[i]>0 else rest
        dependencies[g]=support-{g}
    order=_order(dependencies,budget.tick)
    if order is None:return False
    lengths={};image_total=0
    for g in order:
        budget.tick(len(definitions[g])+1)
        lengths[g]=sum(lengths.get(abs(x),1) for x in definitions[g]);image_total+=2*lengths[g]
    total=0
    for slot,word in enumerate(words):
        budget.tick(len(word)+1)
        if slot not in slots:total+=sum(lengths.get(abs(x),1) for x in word)
    # All expansion sizes are derived before constructing any substituted image.
    budget.size(image_total+total);budget.tick(image_total+total)
    images={}
    for g in order:
        budget.tick();out=[]
        for x in definitions[g]:out.extend(images[x] if abs(x) in children else [x])
        images[g]=out;images[-g]=[-x for x in reversed(out)]
    result=[]
    for slot,word in enumerate(words):
        budget.tick();out=[]
        if slot not in slots:
            for x in word:out.extend(images[x] if abs(x) in children else [x])
        result.append(out)
    words[:]=result;alive.difference_update(children)
    return True
