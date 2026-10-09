"""Independent replay for complete source-bound primitive-pair rounds.

Only source-reconstructed knot presentation states may authorize proper-root
elimination. No producer planning, application or word-normalization helper is
imported. Literal and compressed substitution paths are separately implemented.
"""
from .primitive_power_verify import verify_compressed_terminal, verify_literal_terminal


def _selection(move, alive, verify, check):
    check()
    if type(move) is not dict or set(move)!={'kind','pairs'} or move['kind']!='primitive_projection':
        return None
    pairs = move['pairs']
    if type(pairs) is not list or not pairs or len(pairs)>len(alive)//2:return None
    used,slots,selected = set(),set(),[]
    for proof in pairs:
        check()
        if type(proof) is not dict:return None
        labels = proof.get('generators')
        if (type(labels) is not list or len(labels)!=2
                or any(type(g) is not int or g<=0 for g in labels)
                or labels[0]>=labels[1] or not set(labels)<=alive
                or used.intersection(labels)):
            return None
        if not verify(proof,set(labels)):return None
        # The round contract requires both generators to occur, not a pure power.
        u,v = proof['primitive_vector']
        if not u or not v or proof['relation'] in slots:return None
        used.update(labels);slots.add(proof['relation']);selected.append(proof)
    return selected


def replay_compressed_projection(arena, roots, alive, move):
    selected = _selection(move,alive,lambda p,a: verify_compressed_terminal(arena,roots,a,p),arena.tick)
    if selected is None:return False
    images = {}
    for proof in selected:
        arena.tick()
        a,b = proof['generators'];u,v = proof['primitive_vector']
        # The inverse character if v<0 has the same kernel and fixes orientation.
        character = (v,-u) if v>0 else (-v,u)
        for source,exponent in zip((a,b),character):
            for polarity in (1,-1):
                x = exponent*polarity
                images[source*polarity] = arena.power(arena.letter(a if x>0 else -a),abs(x))
    mapped = {0:0}
    for root in roots:
        pending = [(root,False)]
        while pending:
            arena.tick()
            node,ready = pending.pop()
            if node in mapped:continue
            rule = arena.rules[node]
            if rule[0]=='t':mapped[node] = images.get(rule[1],node)
            elif not ready:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:mapped[node] = arena.concat(mapped[rule[1]],mapped[rule[2]])
    roots[:] = [mapped[root] for root in roots]
    for proof in selected:
        arena.tick()
        roots[proof['relation']] = 0
        alive.remove(proof['generators'][1])
    return True


def replay_literal_projection(words, alive, move, budget):
    selected = _selection(move,alive,lambda p,a: verify_literal_terminal(words,a,p,budget),budget.tick)
    if selected is None:return False
    powers = {}
    for proof in selected:
        budget.tick()
        a,b = proof['generators'];u,v = proof['primitive_vector']
        for g,k in ((a,abs(v)),(b,-u if v>0 else u)):
            powers[g] = a,k;powers[-g] = a,-k
    # Guard the entire projected allocation before constructing any repeated list.
    total = 0
    for word in words:
        budget.tick(len(word)+1)
        total += sum(abs(powers[x][1]) if x in powers else 1 for x in word)
    budget.size(total)
    budget.tick(total)  # Every copied output letter, before allocating repeats.
    result = []
    for word in words:
        out = []
        for letter in word:
            budget.tick()
            if letter in powers:
                a,k = powers[letter];out.extend([a if k>0 else -a]*abs(k))
            else:out.append(letter)
        result.append(out)
    words[:] = result
    for proof in selected:
        budget.tick();words[proof['relation']] = [];alive.remove(proof['generators'][1])
    return True


def _rank_one_header(alive, terminal):
    return (type(terminal) is dict and set(terminal)=={'kind','generator'}
            and terminal['kind']=='rank_one_exponent_zero'
            and type(terminal['generator']) is int and terminal['generator']>0
            and alive=={terminal['generator']})


def verify_compressed_rank_one(arena, roots, alive, terminal):
    arena.tick()
    if not _rank_one_header(alive,terminal):return False
    g = terminal['generator'];totals = {0:0}
    for root in roots:
        pending = [(root,False)]
        while pending:
            arena.tick();node,ready = pending.pop()
            if node in totals:continue
            rule = arena.rules[node]
            if rule[0]=='t':
                if rule[1] not in (g,-g):return False
                totals[node] = 1 if rule[1]==g else -1
            elif not ready:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:totals[node] = totals[rule[1]]+totals[rule[2]]
        if totals[root]:return False
    return True


def verify_literal_rank_one(words, alive, terminal, budget):
    budget.tick()
    if not _rank_one_header(alive,terminal):return False
    g = terminal['generator']
    for word in words:
        total = 0
        for x in word:
            budget.tick()
            if x not in (g,-g):return False
            total += 1 if x==g else -1
        if total:return False
    return True
