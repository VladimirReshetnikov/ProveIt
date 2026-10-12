"""Deterministic fully compressed pattern matching by cut-occurrence AP tables.

Based on Lifshits, arXiv:cs/0604058, Section III. Positions are zero based;
intervals are half open, but an occurrence may touch a cut at either end.
No strings, occurrence lists, or probabilistic fingerprints are expanded.
"""
from math import gcd
from .compressed_words import CompressedLimit


def _last(ap):
    return ap[0]+ap[1]*(ap[2]-1)


def _clip(ap, lo, hi):
    """Restrict starting positions to the inclusive interval [lo, hi]."""
    if ap is None or hi < lo:
        return None
    start, step, count = ap
    if count == 1:
        return ap if lo <= start <= hi else None
    first = max(0, (lo-start+step-1)//step)
    final = min(count-1, (hi-start)//step)
    if final < first:
        return None
    return start+first*step, step if final > first else 0, final-first+1


def _shift(ap, delta):
    return None if ap is None else (ap[0]+delta, ap[1], ap[2])


def _intersect(a, b):
    if a is None or b is None:
        return None
    if a[2] == 1:
        return a if _clip(b, a[0], a[0]) is not None else None
    if b[2] == 1:
        return b if _clip(a, b[0], b[0]) is not None else None
    x, d, _ = a
    y, e, _ = b
    divisor = gcd(d, e)
    if (y-x) % divisor:
        return None
    reduced = e//divisor
    residue = 0 if reduced == 1 else ((y-x)//divisor*pow(d//divisor, -1, reduced)) % reduced
    period = d*reduced
    base = x+d*residue
    lo, hi = max(x, y), min(_last(a), _last(b))
    first = base+((lo-base+period-1)//period)*period
    if first > hi:
        return None
    count = (hi-first)//period+1
    return first, period if count > 1 else 0, count


def _one_ap(parts, tick):
    """Merge ordered, endpoint-disjoint APs known to have a common cut.

    The cardinality check prevents silently filling gaps if an invariant fails.
    """
    first, final, step, count = None, None, 0, 0
    for ap in parts:
        tick()
        if ap is None:
            continue
        start, difference, size = ap
        if first is None:
            first = start
        elif start < final:
            raise ArithmeticError('overlapping cut progression interiors')
        count += size-int(final == start)
        step = gcd(step, start-first)
        if size > 1:
            step = gcd(step, difference)
        final = _last(ap)
    if first is None:
        return None
    expected = (final-first)//step+1 if step else 1
    if expected != count:
        raise ArithmeticError('cut occurrences do not form an arithmetic progression')
    return first, step, count


class MatchTable:
    """AP[p,t] stores pattern p occurrences touching the cut of text node t.

    max_nodes also bounds table cells, independently of arena node allocation.
    All operations consume the caller's arena work allowance and cancellation.
    """
    def __init__(self, arena, pattern, text):
        self.arena, self.pattern, self.text = arena, pattern, text
        self.pattern_nodes = arena._reachable([pattern])
        self.text_nodes = arena._reachable([text])
        self.cells = {}
        for p in self.pattern_nodes:
            for t in self.text_nodes:
                arena.tick()
                if arena.lengths[p] > arena.lengths[t]:
                    continue
                if len(self.cells) >= arena.max_nodes:
                    raise CompressedLimit('compressed-match table allowance exhausted')
                self.cells[p, t] = self._cell(p, t)
                arena.stats['match_cells'] = arena.stats.get('match_cells', 0)+1

    def local(self, p, t, alpha, beta):
        """Occurrences wholly in [alpha,beta], of width at most 3*|p|.

        Partition starts at alpha+|p|. Each group shares a cut, so each
        group is one AP, regardless of the number of expanded occurrences.
        """
        arena, length = self.arena, self.arena.lengths[p]
        alpha, beta = max(0, alpha), min(arena.lengths[t], beta)
        if beta-alpha < length:
            return []
        if not length or beta-alpha > 3*length:
            raise ValueError('local matching interval exceeds three pattern lengths')
        groups, pending = [[], []], [(False, t, 0)]
        while pending:
            arena.tick()
            emit, node, offset = pending.pop()
            if emit:
                ap = _clip(_shift(self.cells.get((p, node)), offset), alpha, beta-length)
                groups[0].append(_clip(ap, alpha, alpha+length))
                groups[1].append(_clip(ap, alpha+length+1, beta-length))
                continue
            rule = arena.rules[node]
            if rule[0] == 't':
                pending.append((True, node, offset))
                continue
            left, right = rule[1:]
            cut = offset+arena.lengths[left]
            if min(beta, offset+arena.lengths[node])-max(alpha, cut) >= length:
                pending.append((False, right, cut))
            pending.append((True, node, offset))
            if min(beta, cut)-max(alpha, offset) >= length:
                pending.append((False, left, offset))
        return [ap for group in groups if (ap := _one_ap(group, arena.tick)) is not None]

    def _cell(self, p, t):
        arena = self.arena
        pr, tr = arena.rules[p], arena.rules[t]
        if pr[0] == 't':
            if tr[0] == 't':
                return (0, 0, 1) if pr[1] == tr[1] else None
            left, right = tr[1:]
            cut = arena.lengths[left]
            points = []
            if arena.last[left] == pr[1]:
                points.append((cut-1, 0, 1))
            if arena.first[right] == pr[1]:
                points.append((cut, 0, 1))
            return _one_ap(points, arena.tick)
        left, right = pr[1:]
        ll, rr, total = arena.lengths[left], arena.lengths[right], arena.lengths[p]
        cut, end = arena.lengths[tr[1]], arena.lengths[t]
        results = []
        if ll >= rr:
            candidates = self.local(left, t, cut-total, cut+ll)
            for ap in candidates:
                ap = _clip(ap, max(0, cut-total), min(cut, end-total))
                if ap is None:
                    continue
                endings = _shift(ap, ll)
                last = _last(endings)
                continental = _clip(endings, endings[0], last-rr)
                if continental is not None and self.local(right, t, continental[0], continental[0]+rr):
                    results.append(_shift(continental, -ll))
                seaside = _clip(endings, last-rr+1, last)
                for match in self.local(right, t, last-rr, last+rr):
                    results.append(_shift(_intersect(seaside, match), -ll))
        else:
            candidates = self.local(right, t, cut-rr, cut+total)
            for ap in candidates:
                ap = _clip(ap, max(ll, cut-rr), min(cut+ll, end-rr))
                if ap is None:
                    continue
                first = ap[0]
                seaside = _clip(ap, first, first+ll-1)
                for match in self.local(left, t, first-ll, first+ll):
                    results.append(_shift(_intersect(seaside, _shift(match, ll)), -ll))
                continental = _clip(ap, first+ll, _last(ap))
                if continental is not None and self.local(left, t, continental[0]-ll, continental[0]):
                    results.append(_shift(continental, -ll))
        return _one_ap(results, arena.tick)

    def first(self):
        if not self.pattern:
            return 0
        arena, offsets, answer = self.arena, {self.text: 0}, None
        for t in reversed(self.text_nodes):
            arena.tick()
            offset = offsets[t]
            ap = self.cells.get((self.pattern, t))
            if ap is not None:
                candidate = offset+ap[0]
                answer = candidate if answer is None else min(answer, candidate)
            rule = arena.rules[t]
            if rule[0] == 'c':
                left, right = rule[1:]
                for child, position in ((left, offset), (right, offset+arena.lengths[left])):
                    offsets[child] = min(offsets.get(child, position), position)
        return answer


def first_occurrence(arena, pattern, text):
    """Return the first exact substring position, or None; never decompress."""
    arena.tick()
    if not pattern:
        return 0
    if arena.lengths[pattern] > arena.lengths[text]:
        return None
    if arena.lcp(pattern, text) == arena.lengths[pattern]:
        return 0
    # Try the earliest occurrence of the first signed letter. If the whole
    # pattern matches there, no earlier match is possible. A failed probe
    # falls through to the complete AP table, never a negative conclusion.
    positions = {0: None}
    for node in arena._reachable([text]):
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            positions[node] = 0 if rule[1] == arena.first[pattern] else None
        else:
            left, right = rule[1:]
            positions[node] = positions[left]
            if positions[node] is None and positions[right] is not None:
                positions[node] = arena.lengths[left]+positions[right]
    position = positions[text]
    if position is None or position+arena.lengths[pattern] > arena.lengths[text]:
        return None
    if position and arena.lcp(pattern, arena.slice(text, position, position+arena.lengths[pattern])) == arena.lengths[pattern]:
        arena.stats['match_first_letter_hits'] = arena.stats.get('match_first_letter_hits', 0)+1
        return position
    return MatchTable(arena, pattern, text).first()
