"""Exploratory allocator, exact original except two explicit policy parameters.
Right CI5/CI6 entries are hypotheses until separately verified by runtime.
"""
from collections import defaultdict,Counter
def require(x,m):
    if not x: raise ValueError(m)

def compile_tree(s, b, table, old_src, new_src, *, protected=False, hypothetical_entries=False):
    """Incremental exploratory allocator, adapted from K220 recompile.py.

    K219 has one duplicated subtree role. Unlike the older function-valued
    validator, unchanged nodes may resolve to any of their exact old states.
    This is a decoder-prefix check only, never a primitive/runtime proof.
    """
    groups, _ = b.decoder_map(table, old_src)
    old_states = defaultdict(set)
    for q, nodes in groups.items():
        for n in nodes: old_states[n].add(q)
    node_state = {n: min(qs) for n, qs in old_states.items()}
    live = set()
    def visit(n):
        if s.leaf(n) or n in live: return
        live.add(n); visit(n[0]); visit(n[1])
    visit(new_src)
    origins = {}
    def walk(n, o):
        if s.leaf(n) or o is None or s.leaf(o): return
        if n != o: origins.setdefault(n, o)
        walk(n[0], o[0]); walk(n[1], o[1])
    walk(new_src, old_src)
    origins = {} if protected else {n: o for n, o in origins.items() if o not in live}
    compiled = dict(table); mapped = dict(node_state); mapped[new_src] = 84
    claimed = {84: new_src}; fresh = max(300, max(q for q, _ in table)+1)
    nextfresh = fresh; reused = 0; leaves = {}
    for op in ['CI', 'CD', 'CC', 'CB', 'CH']:
        for arg in ([None] if op == 'CH' else range(10)):
            ch = op, arg
            for bit in (0, 1):
                choices = Counter(table[q, bit] for n, qs in old_states.items() for q in qs if n[bit] == ch)
                direct = [a for a in choices if a[:2] == (bit, 1)]
                if len(direct) == 1: leaves[ch, bit] = direct[0]
                elif ch == ('CC', 1) and bit == 1: leaves[ch, bit] = (0, -1, 1)
                elif ch == ('CC', 2) and bit == 1: leaves[ch, bit] = (0, -1, 16)
                elif ch == ('CB', 1) and bit == 1: leaves[ch, bit] = (0, -1, 40)
    if hypothetical_entries:
        leaves[('CI', 5), 1] = (1, 1, 63)
        leaves[('CI', 6), 1] = (1, 1, 13)
    def go(n):
        nonlocal fresh, reused
        if n in mapped: return mapped[n]
        if n in origins and origins[n] in node_state and len(groups[node_state[origins[n]]]) == 1 and node_state[origins[n]] not in claimed:
            q = node_state[origins[n]]; reused += 1
        else: q = fresh; fresh += 1
        mapped[n] = q; claimed[q] = n
        for bit, ch in enumerate(n):
            if not s.leaf(ch): compiled[q, bit] = (bit, 1, go(ch))
            elif n in origins and origins[n] in node_state and origins[n][bit] == ch:
                compiled[q, bit] = table[node_state[origins[n]], bit]
            elif (ch, bit) in leaves: compiled[q, bit] = leaves[ch, bit]
            else: raise ValueError(('No generic leaf entry', ch, bit, q))
        return q
    for bit, ch in enumerate(new_src):
        compiled[84, bit] = (bit, 1, go(ch)) if not s.leaf(ch) else leaves[ch, bit]
    reach = {0}; todo = [0]
    for q in todo:
        for bit in (0, 1):
            z = compiled[q, bit][2]
            if z != 254 and z not in reach: reach.add(z); todo.append(z)
    compiled = {k: v for k, v in compiled.items() if k[0] in reach}
    gg, _ = b.decoder_map(compiled, new_src)
    for q, nodes in gg.items():
        for n in nodes:
            permitted = old_states[n] if n in old_states and n != new_src else {mapped[n]}
            require(q in permitted, ('Node binding mismatch', q, sorted(permitted)))
    return compiled, {'working_states': len(compiled)//2, 'fresh': fresh-nextfresh,
        'reused': reused, 'aliases': sum(len(ns)-1 for ns in gg.values()),
        'decoder_states': len(gg), 'interior_roles': sum(map(len, gg.values())),
        'scope': 'Raw table and exact decoder-prefix binding only; no runtime or startup validation.'}
