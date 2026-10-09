"""Independent complete forest replay after reconstruction of the source knot.

Arithmetic donor checking is shared with version five. Forest validation,
quotient images and raw substitution do not import producer helpers.
"""
from .primitive_power_verify import verify_compressed_terminal, verify_literal_terminal


def _images(move, alive, verify, check):
    check()
    if type(move) is not dict or set(move)!={'kind','edges'} or move['kind']!='primitive_forest':return None
    edges=move['edges']
    if type(edges) is not list or not edges or len(edges)>=len(alive):return None
    dependents={};eliminated=set();slots=set()
    for edge in edges:
        check()
        if type(edge) is not dict or set(edge)!={'child','proof'}:return None
        child,proof=edge['child'],edge['proof']
        if type(child) is not int or child not in alive or child in eliminated or type(proof) is not dict:return None
        pair=proof.get('generators')
        if (type(pair) is not list or len(pair)!=2 or any(type(g) is not int for g in pair)
                or pair[0]>=pair[1] or not set(pair)<=alive or child not in pair):return None
        if not verify(proof,set(pair)):return None
        i=pair.index(child);unit=proof['primitive_vector'][i];other=proof['primitive_vector'][1-i]
        if abs(unit)!=1 or not other or proof['relation'] in slots:return None
        parent=pair[1-i];factor=-other//unit
        dependents.setdefault(parent,[]).append((child,factor))
        eliminated.add(child);slots.add(proof['relation'])
    # Traverse out from surviving roots. Cycles cannot be reached, so checking
    # that every generator was reached rejects all cyclic components.
    values={g:(g,1) for g in alive if g not in eliminated};queue=list(values);order=[]
    for parent in queue:
        check();anchor,exponent=values[parent]
        for child,factor in dependents.get(parent,()):
            check()
            if child in values:return None
            values[child]=anchor,exponent*factor;queue.append(child);order.append((parent,child,factor))
    if len(values)!=len(alive):return None
    return {g:values[g] for g in eliminated},slots,order


def replay_compressed_forest(arena, roots, alive, move):
    data=_images(move,alive,lambda p,a:verify_compressed_terminal(arena,roots,a,p),arena.tick)
    if data is None:return False
    powers,slots,order=data;images={}
    for parent,child,factor in order:
        arena.tick()
        if parent not in images:
            images[parent]=arena.letter(parent);images[-parent]=arena.letter(-parent)
        for sign in (1,-1):
            source=parent if factor*sign>0 else -parent
            images[child*sign]=arena.power(images[source],abs(factor))
    mapped={0:0}
    for root in roots:
        pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in mapped:continue
            rule=arena.rules[node]
            if rule[0]=='t':mapped[node]=images.get(rule[1],node)
            elif ready:mapped[node]=arena.concat(mapped[rule[1]],mapped[rule[2]])
            else:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
    roots[:]=[mapped[r] for r in roots]
    for slot in slots:arena.tick();roots[slot]=0
    alive.difference_update(powers)
    return True


def replay_literal_forest(words, alive, move, budget):
    data=_images(move,alive,lambda p,a:verify_literal_terminal(words,a,p,budget),budget.tick)
    if data is None:return False
    powers,slots,_=data;total=0
    for word in words:
        budget.tick(len(word)+1)
        for letter in word:
            total+=abs(powers[abs(letter)][1]) if abs(letter) in powers else 1
    budget.size(total);budget.tick(total)
    result=[]
    for word in words:
        out=[]
        for x in word:
            budget.tick()
            if abs(x) in powers:
                anchor,n=powers[abs(x)];n=n if x>0 else -n
                out.extend([anchor if n>0 else -anchor]*abs(n))
            else:out.append(x)
        result.append(out)
    words[:]=result
    for slot in slots:budget.tick();words[slot]=[]
    alive.difference_update(powers)
    return True
