"""Independent leaf/cycle replay for source-established plain-power groups.

Authenticate actual cyclic word shape before using exponent arithmetic. An
inconsistent signed cycle gives torsion, and the recovered knot host supplies
torsion-freeness. Neither a matrix rank alone nor an arbitrary caller flag does.
"""
from collections import deque


def _annihilates(labels, rows, tick):
    adjacency={g:[] for g in labels}
    for index,row in enumerate(rows):
        tick()
        for g in row:adjacency[g].append(index)
        if len(row)==1:adjacency[next(iter(row))].append(index)
    # Check that every claimed label belongs to one connected component.
    reached=set();pending=[labels[0]]
    while pending:
        tick();g=pending.pop()
        if g in reached:continue
        reached.add(g)
        for i in adjacency[g]:pending.extend(rows[i])
    if reached!=set(labels):return False
    degree={g:len(adjacency[g]) for g in labels};active=set(range(len(rows)))
    leaves=deque(g for g in labels if degree[g]==1)
    while leaves:
        tick();g=leaves.popleft()
        if degree[g]!=1:continue
        edge=next(i for i in adjacency[g] if i in active);active.remove(edge)
        for h in rows[edge]:
            degree[h]-=1
            if degree[h]==1:leaves.append(h)
    core=[g for g in labels if degree[g]]
    if not core or any(degree[g]!=2 for g in core):return False
    if len(core)==1:
        # One pure-power seed remains after peeling its attached tree.
        return len(active)==1 and len(rows[next(iter(active))])==1
    current=start=core[0];visited=set();left=right=1
    while True:
        tick();choices=[i for i in adjacency[current] if i in active and i not in visited]
        if not choices:return False
        edge=choices[0];visited.add(edge);row=rows[edge]
        if len(row)!=2:return False
        other=next(g for g in row if g!=current)
        left*=row[current];right*=-row[other];current=other
        if current==start:break
    return visited==active and left!=right


def _selection(move, alive, slots, row, tick):
    tick()
    if type(move) is not dict or set(move)!={'kind','components'} or move['kind']!='power_component_delete':return None
    components=move['components']
    if type(components) is not list or not components:return None
    erased=set()
    for proof in components:
        tick()
        if type(proof) is not dict or set(proof)!={'generators','relations'}:return None
        labels,relations=proof['generators'],proof['relations']
        if (type(labels) is not list or len(labels)<3 or any(type(g) is not int or g<=0 for g in labels)
                or labels!=sorted(set(labels)) or not set(labels)<=alive or erased.intersection(labels)
                or type(relations) is not list or len(relations)!=len(labels)
                or any(type(j) is not int or not 0<=j<slots for j in relations)
                or relations!=sorted(set(relations))):return None
        rows=[]
        for slot in relations:
            tick();value=row(slot,labels)
            if value is None:return None
            rows.append(value)
        if not _annihilates(labels,rows,tick):return None
        erased.update(labels)
    return erased if len(erased)<len(alive) else None


def replay_compressed_power_components(arena, roots, alive, move):
    summaries={0:(0,0,0,{})}
    def row(slot,labels):
        root=roots[slot];pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in summaries:continue
            rule=arena.rules[node]
            if rule[0]=='t':summaries[node]=rule[1],rule[1],0,{rule[1]:1}
            elif not ready:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:
                f,l,t,c=summaries[rule[1]];g,h,u,d=summaries[rule[2]]
                if c is None or d is None or len(c.keys()|d.keys())>2:
                    summaries[node]=(f or g,h or l,3,None);continue
                counts=dict(c)
                for x,n in d.items():counts[x]=counts.get(x,0)+n
                summaries[node]=(f or g,h or l,min(3,t+u+int(bool(l and g and l!=g))),counts)
        first,last,changes,counts=summaries[root]
        if (not counts or any(abs(g) not in labels for g in counts)
                or len({abs(g) for g in counts})!=len(counts) or changes+int(first!=last)>2):return None
        return {abs(g):n if g>0 else -n for g,n in counts.items()}
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
    arena.tick(len(roots)+1);output=[mapped[root] for root in roots]
    roots[:]=output;alive.difference_update(erased)
    return True


def replay_literal_power_components(words, alive, move, budget):
    def row(slot,labels):
        word=words[slot]
        if not word:return None
        counts={};changes=0
        for i,x in enumerate(word):
            budget.tick()
            if abs(x) not in labels:return None
            counts[x]=counts.get(x,0)+1;changes+=x!=word[i-1]
        if changes>2 or len({abs(x) for x in counts})!=len(counts):return None
        return {abs(g):n if g>0 else -n for g,n in counts.items()}
    erased=_selection(move,alive,len(words),row,budget.tick)
    if erased is None:return False
    output=[]
    for word in words:
        out=[]
        for x in word:
            budget.tick()
            if abs(x) not in erased:out.append(x)
        output.append(out)
    words[:]=output;alive.difference_update(erased)
    return True
