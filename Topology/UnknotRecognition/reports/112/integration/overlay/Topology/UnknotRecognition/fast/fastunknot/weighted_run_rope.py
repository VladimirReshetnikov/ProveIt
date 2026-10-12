"""Local additive-weight transport on deterministic AVL run sequences.

Coordinates are implicit prefix lengths.  Splitting and joining a sequence
therefore never rewrites the coordinates of an untouched run.  This module
does not authenticate an orbit trace: its caller must do that independently.
Translation transport uses a residue anchor and the discrete derivative;
reflection transport reverses the deleted suffix's run order.  Constant
additions are lazy on whole receiver subtrees: their internal run partition
is never visited, since adding one vector preserves all internal equalities.
"""


class RunRopeError(ValueError):
    """A checked transport operation violates the run-sequence contract."""


class _Node:
    __slots__ = ('left', 'right', 'span', 'height', 'count', 'value', 'lazy',
                 'first_span', 'last_span', 'first_value', 'last_value')

    def __init__(self, span, value=None, left=None, right=None):
        self.left, self.right, self.span, self.value = left, right, span, value
        self.lazy = None
        if left is None:
            self.height = self.count = 1
            self.first_span = self.last_span = span
            self.first_value = self.last_value = value
        else:
            self.height = 1 + max(left.height, right.height)
            self.count = left.count + right.count
            self.first_span, self.last_span = left.first_span, right.last_span
            self.first_value, self.last_value = left.first_value, right.last_value


def _sum(left, right):
    return tuple(a + b for a, b in zip(left, right))


def _add_tree(node, increment):
    """Add one vector in constant structural time, deferring child updates."""
    if node is None or not any(increment):
        return node
    if node.left is None:
        return _Node(node.span, _sum(node.value, increment))
    result = _Node(node.span, left=node.left, right=node.right)
    result.lazy = increment if node.lazy is None else _sum(node.lazy, increment)
    if not any(result.lazy):
        result.lazy = None
    result.first_value = _sum(node.first_value, increment)
    result.last_value = _sum(node.last_value, increment)
    return result


def _push(node):
    if node is None or node.lazy is None:
        return node
    return _branch(_add_tree(node.left, node.lazy), _add_tree(node.right, node.lazy))


def _branch(left, right):
    if left is None:
        return right
    if right is None:
        return left
    return _Node(left.span + right.span, left=left, right=right)


def _height(node):
    return 0 if node is None else node.height


def _balance(left, right):
    """Balance a join whose child heights differ by at most two."""
    if _height(left) > _height(right) + 1:
        left = _push(left)
        if _height(left.left) >= _height(left.right):
            return _branch(left.left, _branch(left.right, right))
        pivot = _push(left.right)
        return _branch(_branch(left.left, pivot.left), _branch(pivot.right, right))
    if _height(right) > _height(left) + 1:
        right = _push(right)
        if _height(right.right) >= _height(right.left):
            return _branch(_branch(left, right.left), right.right)
        pivot = _push(right.left)
        return _branch(_branch(left, pivot.left), _branch(pivot.right, right.right))
    return _branch(left, right)


def _join(left, right):
    """AVL concatenation, without inspecting or coalescing boundary values."""
    if left is None:
        return right
    if right is None:
        return left
    if left.height > right.height + 1:
        left = _push(left)
        return _balance(left.left, _join(left.right, right))
    if right.height > left.height + 1:
        right = _push(right)
        return _balance(_join(left, right.left), right.right)
    return _branch(left, right)


def _split(node, point):
    """Split at a prefix length, sharing all unaffected subtrees."""
    if node is None:
        if point != 0:
            raise RunRopeError('split outside an empty run sequence')
        return None, None
    if point == 0:
        return None, node
    if point == node.span:
        return node, None
    if not 0 < point < node.span:
        raise RunRopeError('split outside a run sequence')
    if node.left is None:
        return _Node(point, node.value), _Node(node.span - point, node.value)
    node = _push(node)
    if point < node.left.span:
        left, middle = _split(node.left, point)
        return left, _join(middle, node.right)
    if point == node.left.span:
        return node.left, node.right
    middle, right = _split(node.right, point - node.left.span)
    return _join(node.left, middle), right


def _concat(left, right):
    """Concatenate canonical runs, coalescing just the touching pair."""
    if left is None or right is None:
        return _join(left, right)
    if left.last_value != right.first_value:
        return _join(left, right)
    a, b, value = left.last_span, right.first_span, left.last_value
    prefix, _ = _split(left, left.span - a)
    _, suffix = _split(right, b)
    return _join(_join(prefix, _Node(a + b, value)), suffix)


def _segments(node, reverse=False):
    """Visit only this subtree's leaves in either direction."""
    stack = [(node, None)] if node is not None else []
    while stack:
        current, inherited = stack.pop()
        if current.left is None:
            value = current.value if inherited is None else _sum(current.value, inherited)
            yield current.span, value
        else:
            if current.lazy is not None:
                inherited = (current.lazy if inherited is None else
                             _sum(current.lazy, inherited))
            if reverse:
                stack.extend(((current.left, inherited), (current.right, inherited)))
            else:
                stack.extend(((current.right, inherited), (current.left, inherited)))


def _append(entries, span, value):
    if span <= 0:
        if span < 0:
            raise RunRopeError('negative run length')
        return
    if entries and entries[-1][1] == value:
        entries[-1] = (entries[-1][0] + span, value)
    else:
        entries.append((span, value))


def _build(entries):
    def build(first, stop):
        if stop == first:
            return None
        if stop == first + 1:
            span, value = entries[first]
            return _Node(span, value)
        middle = (first + stop) // 2
        return _branch(build(first, middle), build(middle, stop))
    return build(0, len(entries))


def from_runs(runs, poll=lambda: None):
    """Build once from a canonical covering run list already checked by caller."""
    entries, position = [], 0
    for lo, hi, value in runs:
        poll()
        if lo != position or hi <= lo:
            raise RunRopeError('initial runs do not cover their interval')
        _append(entries, hi - lo, value)
        position = hi
    return _build(entries)


def to_runs(root):
    """Materialize for diagnostics only; transport does not call this helper."""
    answer, position = [], 0
    for span, value in _segments(root):
        answer.append((position, position + span, value))
        position += span
    return answer


def _range_adds(target, additions, poll, metrics):
    """Add canonical consecutive intervals without enumerating receiver runs."""
    retained, tail = None, target
    for span, value in additions:
        poll()
        middle, tail = _split(tail, span)
        middle = _add_tree(middle, value)
        retained = _concat(retained, middle)
        metrics['range_adds'] += 1
    if tail is not None:
        raise RunRopeError('local additions do not cover their receiver interval')
    return retained


class LocalTransport:
    """A per-replay transport owner; no source or proof survives the call."""

    def __init__(self, metrics=None):
        self.metrics = {} if metrics is None else metrics
        self.metrics.update(initial_runs=0, maximum_runs=0, folds=0,
                            source_runs=0, target_runs=0, range_adds=0,
                            static_gaps=0, emitted_runs=0)

    def prepare(self, runs, poll):
        root = from_runs(runs, poll)
        self.metrics['initial_runs'] = self.metrics['maximum_runs'] = len(runs)
        return root

    def _record(self, root):
        self.metrics['maximum_runs'] = max(
            self.metrics['maximum_runs'], 0 if root is None else root.count)
        return root

    def translation(self, root, size, cut, period, dimension, poll):
        """Fold suffix jumps modulo period, anchored at its first residue."""
        if root is None or root.span != size or not 0 < period <= cut < size:
            raise RunRopeError('invalid translation weight fold')
        prefix, suffix = _split(root, cut)
        before, target = _split(prefix, cut - period)
        self.metrics['folds'] += 1
        self.metrics['source_runs'] += suffix.count
        self.metrics['target_runs'] += target.count
        mapped, anchor, position = [], (0,) * dimension, 0
        preceding = (0,) * dimension
        for span, value in _segments(suffix):
            poll()
            stop = position + span
            multiplicity = (stop - 1) // period - (position - 1) // period
            anchor = _sum(anchor, tuple(multiplicity * x for x in value))
            # Form the actual jump before reducing its coordinate modulo p.
            # Adjacent source endpoints cancel here, leaving at most S+1
            # mapped jump records for S canonical suffix runs.
            mapped.append((position % period,
                           tuple(a - b for a, b in zip(value, preceding))))
            position = stop
            preceding = value
        mapped.append((position % period, tuple(-x for x in preceding)))
        mapped.sort(key=lambda item: item[0])
        added, previous, current = [], 0, anchor
        index = 0
        while index < len(mapped):
            poll()
            point, increment = mapped[index]
            index += 1
            while index < len(mapped) and mapped[index][0] == point:
                increment = _sum(increment, mapped[index][1])
                index += 1
            if point == 0:
                continue
            _append(added, point - previous, current)
            current = _sum(current, increment)
            previous = point
        _append(added, period - previous, current)
        replacement = _range_adds(target, added, poll, self.metrics)
        return self._record(_concat(before, replacement))

    def reflection(self, root, size, cut, centre, dimension, poll):
        """Reflect the removed suffix and add only on its retained image."""
        left, right = centre - size + 1, centre - cut + 1
        if (root is None or root.span != size or not 0 <= left < right <= cut < size):
            raise RunRopeError('invalid reflection weight fold')
        prefix, suffix = _split(root, cut)
        before, rest = _split(prefix, left)
        target, after = _split(rest, right - left)
        self.metrics['folds'] += 1
        self.metrics['source_runs'] += suffix.count
        self.metrics['target_runs'] += target.count
        replacement = _range_adds(target, _segments(suffix, reverse=True),
                                  poll, self.metrics)
        return self._record(_concat(_concat(before, replacement), after))

    def contract(self, root, size, gaps, histogram, poll):
        """Delete static gaps without traversing retained run interiors."""
        if (0 if root is None else root.span) != size:
            raise RunRopeError('static gap size differs from run sequence')
        tail, retained, position, removed = root, None, 0, 0
        for lo, hi in gaps:
            poll()
            if not position <= lo <= hi < size:
                raise RunRopeError('static gaps are not ordered disjoint intervals')
            unchanged, rest = _split(tail, lo - position)
            deleted, tail = _split(rest, hi - lo + 1)
            for span, value in _segments(deleted):
                poll()
                histogram[value] += span
                self.metrics['emitted_runs'] += 1
            retained = _concat(retained, unchanged)
            position = hi + 1
            removed += hi - lo + 1
            self.metrics['static_gaps'] += 1
        return self._record(_concat(retained, tail)), size - removed
