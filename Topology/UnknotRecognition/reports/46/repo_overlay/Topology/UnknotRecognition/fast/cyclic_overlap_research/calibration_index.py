"""Exact cyclic relator overlap using a shared capped suffix-link tree.

O(L log(L+1)) expected dictionary/word operations and O(L) auxiliary space.
The maximum guaranteed gain is exact; tie choices may differ from the old SAM.
Only independent replay of a complete presentation trace can certify a knot.
"""
from bisect import bisect_right


def _insert_best(entries, record, slot_position):
    if entries is None:
        return [record]
    slot = record[slot_position]
    for k, old in enumerate(entries):
        if old[slot_position] == slot:
            if record >= old:
                return entries
            entries[k] = record
            entries.sort()
            return entries
    entries.append(record)
    entries.sort()
    if len(entries) > 2:
        entries.pop()
    return entries


def joint_overlap_move(words, budget, *, stats=None):
    """A largest positive 2*overlap-donor_length, excluding self-donors."""
    nonempty = [(i, word) for i, word in enumerate(words) if word]
    budget.tick(len(words)+1)
    if len(nonempty) < 2:
        return None
    lengths, links, edges, records = [0], [-1], [{}], [None]
    last = transitions = cloned = 0
    separator = object()
    total = sum(len(w) for _, w in nonempty)

    def append_letter(x, record=None):
        nonlocal last, transitions, cloned
        budget.tick()
        current = len(lengths)
        lengths.append(lengths[last]+1)
        links.append(0)
        edges.append({})
        records.append(None if record is None else [record])
        state = last
        while state >= 0 and x not in edges[state]:
            budget.tick()
            edges[state][x] = current
            transitions += 1
            state = links[state]
        if state >= 0:
            target = edges[state][x]
            if lengths[state]+1 == lengths[target]:
                links[current] = target
            else:
                clone = len(lengths)
                budget.tick(len(edges[target])+1)
                lengths.append(lengths[state]+1)
                links.append(links[target])
                edges.append(dict(edges[target]))
                records.append(None)
                transitions += len(edges[target])
                cloned += 1
                while state >= 0 and edges[state].get(x) == target:
                    budget.tick()
                    edges[state][x] = clone
                    state = links[state]
                links[current] = links[target] = clone
        last = current

    for slot, word in nonempty:
        size = len(word)
        budget.tick(size+1)
        for end in range(2*size-1):
            record = (size, size, slot, False, end) if end >= size-1 else None
            append_letter(word[end % size], record)
        append_letter(separator)
    # Inverses need not be inserted into the index. Each inverse window is
    # represented by its longest suffix occurring anywhere in the indexed
    # positive targets; shorter candidate overlaps follow the suffix links.
    inverse_marks = 0
    for slot, word in nonempty:
        size, state, matched = len(word), 0, 0
        for end in range(2*size-1):
            budget.tick()
            x = -word[size-1-(end % size)]
            while state and x not in edges[state]:
                budget.tick()
                state = links[state]
                matched = min(matched, lengths[state])
            if x in edges[state]:
                state = edges[state][x]
                matched += 1
            else:
                matched = 0
            if end >= size-1 and matched:
                record = (min(matched, size), size, slot, True, end)
                if records[state] is None:
                    records[state] = [record]
                else:
                    records[state].append(record)
                inverse_marks += 1
    states = len(lengths)
    children = [[] for _ in lengths]
    for v in range(1, states):
        children[links[v]].append(v)
    donors, targets = [None]*states, [None]*states
    caps = {}
    path, path_lengths, postorder = [], [], []
    stack = [(0, False)]
    marked = 0
    while stack:
        v, leaving = stack.pop()
        budget.tick()
        if leaving:
            path.pop()
            path_lengths.pop()
            postorder.append(v)
            continue
        path.append(v)
        path_lengths.append(lengths[v])
        stack.append((v, True))
        stack.extend((child, False) for child in reversed(children[v]))
        for cap, size, slot, inverse, end in records[v] or ():
            marked += 1
            budget.tick(len(path).bit_length()+1)
            after = bisect_right(path_lengths, cap)
            record = (size, slot, inverse, end)
            target_record = None if inverse else (slot, end, size)
            if path_lengths[after-1] == cap:
                at = path[after-1]
                donors[at] = _insert_best(donors[at], record, 1)
                if target_record is not None:
                    targets[at] = _insert_best(targets[at], target_record, 0)
            else:
                child = path[after]
                edge_caps = caps.setdefault(child, {})
                pair = edge_caps.get(cap)
                if pair is None:
                    pair = [None, None]
                    edge_caps[cap] = pair
                pair[0] = _insert_best(pair[0], record, 1)
                if target_record is not None:
                    pair[1] = _insert_best(pair[1], target_record, 0)
    best_key, best = None, None
    evaluated = 0

    def candidate(depth, ds, ts):
        nonlocal best_key, best, evaluated
        if ds is None or ts is None or depth == 0:
            return
        for size, donor, inverse, dend in ds:
            gain = 2*depth-size
            if gain <= 0:
                continue
            for target, tend, tsize in ts:
                if donor == target:
                    continue
                evaluated += 1
                dstart, tstart = (dend-depth+1) % size, (tend-depth+1) % tsize
                key = (-gain, donor, inverse, target, tstart, dstart)
                if best_key is None or key < best_key:
                    best_key = key
                    best = dict(kind='relator', target=target, donor=donor,
                        target_rotation=tstart, donor_rotation=dstart,
                        inverse=inverse, overlap=depth)

    for v in postorder:
        budget.tick()
        ds, ts = donors[v], targets[v]
        candidate(lengths[v], ds, ts)
        edge_caps = caps.get(v)
        if edge_caps is not None:
            budget.tick(len(edge_caps)*(len(edge_caps).bit_length()+1))
            for depth in sorted(edge_caps, reverse=True):
                cds, cts = edge_caps[depth]
                for record in cds or ():
                    ds = _insert_best(ds, record, 1)
                for record in cts or ():
                    ts = _insert_best(ts, record, 0)
                candidate(depth, ds, ts)
        if v:
            parent = links[v]
            for record in ds or ():
                donors[parent] = _insert_best(donors[parent], record, 1)
            for record in ts or ():
                targets[parent] = _insert_best(targets[parent], record, 0)
    if stats is not None:
        cap_count = sum(map(len, caps.values()))
        stats.update(input_slots=len(words), nonempty_relators=len(nonempty),
            total_length=total, indexed_letters=2*total,
            automaton_states=states, transitions=transitions,
            clones=cloned, marked_rotations=marked, inverse_marks=inverse_marks,
            terminal_caps=cap_count, capped_tree_nodes=states+cap_count,
            evaluated_pairs=evaluated, best_gain=0 if best is None else -best_key[0])
    budget.tick()
    return best


class _PreludeLimit(RuntimeError):
    pass


class _PreludeBudget:
    def __init__(self, shared, limit):
        self.shared, self.limit, self.work = shared, limit, 0

    def tick(self, amount=1):
        self.shared.tick(amount)
        self.work += amount
        if self.work > self.limit:
            raise _PreludeLimit


def bounded_overlap_move(words, budget, *, stats=None, coefficient=2):
    from .relator_overlap import _automaton

    if type(coefficient) is not int or coefficient < 0:
        raise ValueError("coefficient must be a nonnegative integer")
    nonempty = [(i, w) for i, w in enumerate(words) if w]
    budget.tick(len(words)+1)
    total = sum(len(w) for _, w in nonempty)
    limit = coefficient*max(1, total)*(total+1).bit_length()
    local = _PreludeBudget(budget, limit)
    best_gain, best = 0, None
    automata = pair_scans = 0
    if len(nonempty) < 2:
        if stats is not None:
            stats.update(backend='prelude', prelude_work=0, prelude_limit=limit,
                donor_automata=0, pair_scans=0, total_length=total,
                nonempty_relators=len(nonempty), best_gain=0)
        return None
    try:
        local.tick(len(nonempty)*(len(nonempty).bit_length()+1))
        for donor, word in sorted(nonempty, key=lambda item: (-len(item[1]), item[0])):
            if len(word) <= best_gain:
                break
            for inverse in (False, True):
                local.tick(len(word)+1)
                source = [-x for x in reversed(word)] if inverse else word
                lengths, links, edges, ends = _automaton(source, local)
                automata += 1
                for target, other in nonempty:
                    local.tick()
                    if target == donor or 2*min(len(other),len(word))-len(word) <= best_gain:
                        continue
                    pair_scans += 1
                    state = matched = 0
                    for position in range(2*len(other)-1):
                        local.tick()
                        x = other[position % len(other)]
                        while state and x not in edges[state]:
                            local.tick()
                            state = links[state]
                            matched = min(matched, lengths[state])
                        if x in edges[state]:
                            state = edges[state][x]
                            matched += 1
                        else:
                            matched = 0
                        overlap = min(matched, len(word), len(other))
                        gain = 2*overlap-len(word)
                        if gain > best_gain:
                            best_gain = gain
                            best = dict(kind='relator', target=target, donor=donor,
                                target_rotation=(position-overlap+1) % len(other),
                                donor_rotation=(ends[state]-overlap+1) % len(word),
                                inverse=inverse, overlap=overlap)
        backend = 'prelude'
    except _PreludeLimit:
        shared_stats = {}
        best = joint_overlap_move(words, budget, stats=shared_stats)
        best_gain = 0 if best is None else 2*best['overlap']-len(words[best['donor']])
        backend = 'joint-index'
        if stats is not None:
            stats['joint'] = shared_stats
    if stats is not None:
        stats.update(backend=backend, prelude_work=local.work, prelude_limit=limit,
            donor_automata=automata, pair_scans=pair_scans, total_length=total,
            nonempty_relators=len(nonempty), best_gain=best_gain)
    return best
