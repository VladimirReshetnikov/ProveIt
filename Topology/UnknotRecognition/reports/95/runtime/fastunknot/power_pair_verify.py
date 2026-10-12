"""Independent power-row checking for source-established knot-group states.

No producer summaries, extraction or application helpers are used here.
Nonzero determinants prove torsion, not identity in arbitrary groups. Only a
verified knot presentation prefix authorizes this torsion-free deletion rule.
"""


def _selection(move, alive, slots, row, tick):
    tick()
    if type(move) is not dict or set(move)!={'kind','pairs'} or move['kind']!='power_pair_delete':return None
    proofs=move['pairs']
    if type(proofs) is not list or not proofs or 2*len(proofs)>=len(alive):return None
    erased=set()
    for proof in proofs:
        tick()
        if type(proof) is not dict or set(proof)!={'generators','relations'}:return None
        labels,relations=proof['generators'],proof['relations']
        if (type(labels) is not list or len(labels)!=2 or any(type(g) is not int for g in labels)
                or not 0<labels[0]<labels[1] or not set(labels)<=alive or erased.intersection(labels)
                or type(relations) is not list or len(relations)!=2
                or any(type(j) is not int or not 0<=j<slots for j in relations)
                or relations[0]==relations[1]):return None
        first=row(relations[0],labels);second=row(relations[1],labels)
        if first is None or second is None or first[0]*second[1]==first[1]*second[0]:return None
        erased.update(labels)
    return erased


def replay_compressed_power_pairs(arena, roots, alive, move):
    # Count cyclic signed-letter transitions, capped at three. A valid donor
    # has one run, or exactly two cyclic runs on distinct absolute generators.
    summaries={0:(0,0,0,{})}
    def row(slot,labels):
        root=roots[slot];pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in summaries:continue
            rule=arena.rules[node]
            if rule[0]=='t':summaries[node]=(rule[1],rule[1],0,{rule[1]:1})
            elif not ready:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:
                f,l,t,c=summaries[rule[1]];g,h,u,d=summaries[rule[2]]
                if c is None or d is None or len(c.keys()|d.keys())>2:
                    summaries[node]=(f or g,h or l,3,None);continue
                counts=dict(c)
                for x,n in d.items():counts[x]=counts.get(x,0)+n
                summaries[node]=(f or g,h or l,min(3,t+u+int(bool(l and g and l!=g))),counts)
        first,last,changes,counts=summaries[root]
        if not counts or len(counts)>2 or any(abs(g) not in labels for g in counts):return None
        if len({abs(g) for g in counts})!=len(counts):return None
        if changes+int(first!=last)>2:return None
        return tuple(counts.get(g,0)-counts.get(-g,0) for g in labels)
    erased=_selection(move,alive,len(roots),row,arena.tick)
    if erased is None:return False
    mapped={0:0}
    for root in roots:
        pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in mapped:continue
            rule=arena.rules[node]
            if rule[0]=='t':mapped[node]=0 if abs(rule[1]) in erased else node
            elif not ready:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:mapped[node]=arena.concat(mapped[rule[1]],mapped[rule[2]])
    output=[mapped[root] for root in roots]
    roots[:]=output;alive.difference_update(erased)
    return True


def replay_literal_power_pairs(words, alive, move, budget):
    def row(slot,labels):
        word=words[slot]
        if not word:return None
        counts={};changes=0
        for i,x in enumerate(word):
            budget.tick()
            if abs(x) not in labels:return None
            counts[x]=counts.get(x,0)+1;changes+=x!=word[i-1]
        if changes>2 or len({abs(x) for x in counts})!=len(counts):return None
        return tuple(counts.get(g,0)-counts.get(-g,0) for g in labels)
    erased=_selection(move,alive,len(words),row,budget.tick)
    if erased is None:return False
    result=[]
    for word in words:
        out=[]
        for x in word:
            budget.tick()
            if abs(x) not in erased:out.append(x)
        result.append(out)
    words[:]=result;alive.difference_update(erased)
    return True
