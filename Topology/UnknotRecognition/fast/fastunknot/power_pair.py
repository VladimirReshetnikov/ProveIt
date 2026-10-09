"""Plain-power annihilation in source-established torsion-free presentations.

This internal producer is not an arbitrary-group decision procedure. Two
noncollinear power rows imply torsion; the knot host supplies torsion-freeness.
Raw cyclic two-run donors are recognized without expanding or cancelling words.
"""


def power_rows(arena, roots, alive, cache=None):
    """Exact current-slot cyclic one/two-run rows, sharing immutable metadata."""
    if cache is None:cache={}
    runs=cache.setdefault('power_pair_runs',{0:()})
    for root in roots:
        pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in runs:continue
            rule=arena.rules[node]
            if rule[0]=='t':runs[node]=((rule[1],1),)
            elif not ready:
                pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:
                left,right=runs[rule[1]],runs[rule[2]]
                if left is None or right is None:runs[node]=None;continue
                row=list(left)
                for letter,count in right:
                    if row and row[-1][0]==letter:row[-1]=(letter,row[-1][1]+count)
                    else:row.append((letter,count))
                runs[node]=tuple(row) if len(row)<=3 else None
    rows=[]
    for slot,root in enumerate(roots):
        arena.tick();row=runs[root]
        if not row:continue
        row=list(row)
        if len(row)>1 and row[0][0]==row[-1][0]:
            row[0]=(row[0][0],row[0][1]+row.pop()[1])
        if len(row)>2 or any(abs(g) not in alive for g,n in row):continue
        if len(row)==1:
            g,n=row[0];rows.append((slot,((abs(g),n if g>0 else -n),)));continue
        if abs(row[0][0])==abs(row[1][0]):continue
        values={abs(g):n if g>0 else -n for g,n in row};pair=tuple(sorted(values))
        rows.append((slot,tuple((g,values[g]) for g in pair)))
    return rows


def plan_power_pairs(arena, roots, alive, cache=None, *, _prepared=None):
    rows=power_rows(arena,roots,alive,cache) if _prepared is None else _prepared
    groups={};pure={}
    for slot,row in rows:
        arena.tick()
        if len(row)==1:
            g,n=row[0];pure.setdefault(g,(slot,n));continue
        (a,u),(b,v)=row
        groups.setdefault((a,b),[]).append((slot,u,v))
    selected=[];used=set()
    for pair,rows in sorted(groups.items()):
        arena.tick()
        if used.intersection(pair) or len(alive)-len(used)<3:continue
        a,b=pair
        if a in pure:rows.append((pure[a][0],pure[a][1],0))
        if b in pure:rows.append((pure[b][0],0,pure[b][1]))
        first=rows[0]
        for row in rows[1:]:
            arena.tick();arena.stats['power_pair_minor_tests']=arena.stats.get('power_pair_minor_tests',0)+1
            if first[1]*row[2]!=first[2]*row[1]:
                selected.append(dict(generators=list(pair),relations=[first[0],row[0]]));used.update(pair);break
    arena.stats['power_pair_attempts']=arena.stats.get('power_pair_attempts',0)+1
    return selected


def apply_power_pairs(arena, roots, alive, selected):
    erased={g for proof in selected for g in proof['generators']};mapped={0:0}
    for node in arena._reachable(roots):
        arena.tick();rule=arena.rules[node]
        mapped[node]=(0 if abs(rule[1]) in erased else node) if rule[0]=='t' else arena.concat(mapped[rule[1]],mapped[rule[2]])
    output=[mapped[root] for root in roots]
    roots[:]=output;alive.difference_update(erased)
    arena.stats['power_pair_rounds']=arena.stats.get('power_pair_rounds',0)+1
    arena.stats['power_pair_deleted']=arena.stats.get('power_pair_deleted',0)+len(erased)
