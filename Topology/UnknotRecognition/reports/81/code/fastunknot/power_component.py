"""Plain-power graph contradictions under source-established torsion-freeness.

The producer uses rational graph potentials; independent replay strips tree
leaves and checks a signed cycle product. No conjugacy-balancedness premise.
"""
from collections import deque
from fractions import Fraction


def plan_power_components(arena, alive, rows):
    adjacency={}
    for slot,row in rows:
        arena.tick()
        for g,k in row:adjacency.setdefault(g,[]).append((slot,row))
    seen=set();erased=set();selected=[]
    for start in sorted(adjacency):
        arena.tick()
        if start in seen:continue
        values={start:Fraction(1)};queue=deque([start]);tree=[];witness=None
        while queue:
            g=queue.popleft();seen.add(g)
            for slot,row in adjacency[g]:
                arena.tick()
                if len(row)==1:
                    if witness is None:witness=slot
                    continue
                (a,u),(b,v)=row
                other,ratio=(b,Fraction(-u,v)) if g==a else (a,Fraction(-v,u))
                if other not in values:
                    values[other]=values[g]*ratio;queue.append(other);tree.append(slot)
                elif values[other]!=values[g]*ratio and witness is None:witness=slot
        labels=sorted(values)
        if witness is None or len(labels)<3 or len(erased)+len(labels)>=len(alive):continue
        selected.append(dict(generators=labels,relations=sorted(tree+[witness])))
        erased.update(labels)
    arena.stats['power_component_attempts']=arena.stats.get('power_component_attempts',0)+1
    return selected


def apply_power_components(arena, roots, alive, components):
    erased={g for proof in components for g in proof['generators']};mapped={0:0}
    for node in arena._reachable(roots):
        arena.tick();rule=arena.rules[node]
        mapped[node]=(0 if abs(rule[1]) in erased else node) if rule[0]=='t' else arena.concat(mapped[rule[1]],mapped[rule[2]])
    arena.tick(len(roots)+1);output=[mapped[r] for r in roots]
    roots[:]=output;alive.difference_update(erased)
    arena.stats['power_component_rounds']=arena.stats.get('power_component_rounds',0)+1
    arena.stats['power_component_deleted']=arena.stats.get('power_component_deleted',0)+len(erased)
