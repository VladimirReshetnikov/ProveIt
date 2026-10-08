"""Exact cyclic relator-overlap search using suffix automata.

Search only: soundness is established separately by certificate replay.
For R_i=U W and a cyclic conjugate of R_j^(+/-1)=U V, replace
R_i by V^-1 W. Keeping the distinct donor R_j preserves the normal closure.
Only overlaps with 2*len(U)>len(R_j) are proposed, so length decreases.
"""


def _automaton(word, budget):
    """Suffix automaton of word+word[:-1], with occurrence end positions."""
    lengths, links, edges, ends, last = [0], [-1], [{}], [-1], 0
    for position in range(2*len(word)-1):
        budget.tick()
        x = word[position % len(word)]
        current = len(lengths)
        lengths.append(lengths[last]+1)
        links.append(0)
        edges.append({})
        ends.append(position)
        state = last
        while state >= 0 and x not in edges[state]:
            budget.tick()
            edges[state][x] = current
            state = links[state]
        if state >= 0:
            target = edges[state][x]
            if lengths[state]+1 == lengths[target]:
                links[current] = target
            else:
                clone = len(lengths)
                budget.tick(len(edges[target])+1)
                lengths.append(lengths[state]+1)
                edges.append(dict(edges[target]))
                links.append(links[target])
                ends.append(ends[target])
                while state >= 0 and edges[state].get(x) == target:
                    budget.tick()
                    edges[state][x] = clone
                    state = links[state]
                links[current] = links[target] = clone
        last = current
    return lengths, links, edges, ends


def overlap_move(words, budget):
    """Return a largest guaranteed shortening, or None; no substring expansion.

    O(n + m L) dictionary operations for n slots, m nonempty relators and total length L,
    and O(L) auxiliary space. Signed letters are exact Python integers.
    Matches are capped at both cyclic word lengths; multiple wraps cannot
    masquerade as occurrences. Ties follow donor, sign, target, scan order.
    """
    best_gain, best = 0, None
    nonempty = [(i, w) for i, w in enumerate(words) if w]
    for donor, word in nonempty:
        budget.tick(len(word)+1)
        for inverse in (False, True):
            source = [-x for x in reversed(word)] if inverse else word
            lengths, links, edges, ends = _automaton(source, budget)
            for target, other in nonempty:
                if target == donor or 2*len(other)-len(word) <= best_gain:
                    continue
                state = matched = 0
                for position in range(2*len(other)-1):
                    budget.tick()
                    x = other[position % len(other)]
                    while state and x not in edges[state]:
                        budget.tick()
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
    budget.tick()
    return best


def apply_overlap(words, move, budget, reduce):
    """Producer application; checker does not call this helper."""
    target, donor = words[move['target']], words[move['donor']]
    if move['inverse']:
        donor = [-x for x in reversed(donor)]
    a, b, overlap = move['target_rotation'], move['donor_rotation'], move['overlap']
    target = target[a:]+target[:a]
    donor = donor[b:]+donor[:b]
    budget.tick(overlap+1)
    if target[:overlap] != donor[:overlap]:
        raise ArithmeticError('suffix-automaton overlap failed literal comparison')
    replacement = [-x for x in reversed(donor[overlap:])] + target[overlap:]
    words[move['target']] = reduce(replacement, budget)
