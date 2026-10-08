"""Exact singular-safe responses along a reverse suffix filtration.

This research interface compiles every suffix, rather than rebuilding a dense
Laplacian for each observed stage.  Inserting one crossing adds two black face
fragments, merges only open fragments, and closes at most a constant number of
fragments.  Old closed fragments can never be touched by subsequent insertions.

Over a checked prime field, a response retains its interior radical and a
matrix on that radical plus the open black fragments and one grounding anchor.
Only newly closed coordinates need elimination.  A radical of dimension at
least the number of retained terminals contains a permanent nullvector, so a
zero response remains zero under every future boundary attachment.

For maximum dart frontier W, all n suffix responses take O(n*(W+1)**2) field
operations and O(n*(W+1)**2) stored field elements.  The iterator retains just
O((W+1)**2) field elements besides O(n) geometry.  These are response compilation
bounds, not bounds on scanner width, state count, or unknot recognition.

The arithmetic works also in characteristic two; residue-four Jones inference
requires odd moduli and is deliberately not performed here.  No recognizer
driver imports or dispatches to this experimental module.
"""


def _noop():
    pass


class ResponseBudget(RuntimeError):
    """A requested frontier or retained-field-element allowance was exhausted."""


def _allowance(value, name):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name + " must be a nonnegative integer or None")


def _prime(value, check):
    check()
    if type(value) is not int or not 2 <= value < 1 << 31:
        raise ValueError("modulus must be a prime less than 2**31")
    if value == 2:
        return value
    if not value % 2:
        raise ValueError("modulus is composite")
    for divisor in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        check()
        if value == divisor:
            return value
        if value % divisor == 0:
            raise ValueError("modulus is composite")
    odd, power = value - 1, 0
    while odd % 2 == 0:
        check()
        odd //= 2
        power += 1
    # These bases are deterministic below 4,759,123,141.
    for base in (2, 7, 61):
        check()
        if base % value == 0:
            continue
        residue = pow(base, odd, value)
        if residue in (1, value - 1):
            continue
        for _ in range(power - 1):
            check()
            residue = residue * residue % value
            if residue == value - 1:
                break
        else:
            raise ValueError("modulus is composite")
    return value


def _determinant(matrix, prime, check):
    answer = 1
    for column in range(len(matrix)):
        check()
        pivot = next((i for i in range(column, len(matrix))
                      if matrix[i][column]), None)
        if pivot is None:
            return 0
        if pivot != column:
            matrix[pivot], matrix[column] = matrix[column], matrix[pivot]
            answer = -answer
        diagonal = matrix[column][column]
        answer = answer * diagonal % prime
        inverse = pow(diagonal, -1, prime)
        for i in range(column + 1, len(matrix)):
            check()
            coefficient = matrix[i][column] * inverse % prime
            for j in range(column + 1, len(matrix)):
                check()
                matrix[i][j] = (matrix[i][j] - coefficient * matrix[column][j]) % prime
    return answer


def _swap(matrix, first, second, check):
    if first != second:
        matrix[first], matrix[second] = matrix[second], matrix[first]
        for row in matrix:
            check()
            row[first], row[second] = row[second], row[first]


class StreamingResponse:
    """Immutable exterior determinant response for a graph insertion stream.

    Create with ``empty(prime)``.  Each ``advance`` adds new terminal vertices
    and edges, identifies terminals, and forgets some of them.  Previously
    forgotten vertices MUST NOT be identified or receive new edges.  The
    geometric compiler below proves this contract for reverse knot suffixes.

    Vertex names are integers.  ``identifications`` maps every old/new terminal
    to its new name; ``keep`` lists the new names which remain terminals.  An
    anchor must remain, so ``keep`` is nonempty.  ``query`` grounds the first
    block in a supplied terminal partition and returns the tree cofactor.
    """

    __slots__ = ("prime", "terminals", "radical", "factor", "matrix", "zero", "stats")

    def __setattr__(self, name, value):
        raise AttributeError("responses are immutable")

    def __delattr__(self, name):
        raise AttributeError("responses are immutable")

    @classmethod
    def _make(cls, prime, terminals, radical, factor, matrix, zero, stats):
        result = cls()
        for name, value in zip(cls.__slots__, (prime, tuple(terminals), radical,
                                              factor, tuple(tuple(r) for r in matrix),
                                              zero, tuple(sorted(stats.items())))):
            object.__setattr__(result, name, value)
        return result

    @classmethod
    def empty(cls, prime=65521, check=None):
        check = _noop if check is None else check
        prime = _prime(prime, check)
        return cls._make(prime, (), 0, 1, (), False,
                         dict(updates=0, one_pivots=0, two_pivots=0,
                              elimination_updates=0, max_dimension=0,
                              max_new_interior=0, max_radical=0))

    def advance(self, added, edges, identifications, keep, check=None):
        """Return a fully completed new response; never mutate the old one."""
        check = _noop if check is None else check
        check()
        added, keep, edges = tuple(added), tuple(keep), tuple(edges)
        names = self.terminals + added
        if any(type(v) is not int for v in names + keep):
            raise ValueError("vertex names must be integers")
        if len(set(names)) != len(names) or len(set(keep)) != len(keep) or not keep:
            raise ValueError("vertices must be distinct and a terminal anchor must remain")
        if set(identifications) != set(names):
            raise ValueError("identifications must name every current terminal")
        if any(type(v) is not int for v in identifications.values()):
            raise ValueError("identified names must be integers")
        image = set(identifications.values())
        if not set(keep) <= image:
            raise ValueError("cannot retain an unknown terminal")
        for edge in edges:
            check()
            if (len(edge) != 3 or any(type(v) is not int for v in edge)
                    or edge[0] not in identifications or edge[1] not in identifications):
                raise ValueError("new edges must join current terminals")
        stats = dict(self.stats)
        stats["updates"] += 1
        forgotten = sorted(image - set(keep))
        stats["max_new_interior"] = max(stats["max_new_interior"], len(forgotten))
        if self.zero:
            check()
            return self._make(self.prime, keep, 0, 0, (), True, stats)
        r, prime = self.radical, self.prime
        vertices = forgotten + list(keep)
        ids = {v: r + i for i, v in enumerate(vertices)}
        size, interior = r + len(vertices), r + len(forgotten)
        stats["max_dimension"] = max(stats["max_dimension"], size)
        matrix = []
        for _ in range(size):
            check()
            matrix.append([0] * size)
        indices = list(range(r)) + [ids[identifications[v]] for v in self.terminals]
        for i, left in enumerate(indices):
            check()
            for j, right in enumerate(indices):
                check()
                matrix[left][right] = (matrix[left][right] + self.matrix[i][j]) % prime
        for a, b, weight in edges:
            check()
            u, v = ids[identifications[a]], ids[identifications[b]]
            if u != v:
                matrix[u][u] = (matrix[u][u] + weight) % prime
                matrix[v][v] = (matrix[v][v] + weight) % prime
                matrix[u][v] = (matrix[u][v] - weight) % prime
                matrix[v][u] = (matrix[v][u] - weight) % prime
        factor, eliminated = self.factor, 0
        while eliminated < interior:
            check()
            k = eliminated
            diagonal = None
            for i in range(k, interior):
                check()
                if matrix[i][i]:
                    diagonal = i
                    break
            if diagonal is not None:
                _swap(matrix, k, diagonal, check)
                pivot = matrix[k][k]
                inverse = pow(pivot, -1, prime)
                factor = factor * pivot % prime
                for i in range(k + 1, size):
                    check()
                    coefficient = matrix[i][k] * inverse % prime
                    for j in range(i, size):
                        check()
                        value = (matrix[i][j] - coefficient * matrix[k][j]) % prime
                        matrix[i][j] = matrix[j][i] = value
                        stats["elimination_updates"] += 1
                eliminated += 1
                stats["one_pivots"] += 1
                continue
            pair = None
            for i in range(k, interior):
                check()
                for j in range(i + 1, interior):
                    check()
                    if matrix[i][j]:
                        pair = (i, j)
                        break
                if pair is not None:
                    break
            if pair is None:
                break
            first, second = pair
            _swap(matrix, k, first, check)
            _swap(matrix, k + 1, second, check)
            pivot = matrix[k][k + 1]
            inverse = pow(pivot, -1, prime)
            factor = -factor * pivot * pivot % prime
            for i in range(k + 2, size):
                check()
                left = matrix[i][k] * inverse % prime
                right = matrix[i][k + 1] * inverse % prime
                for j in range(i, size):
                    check()
                    value = (matrix[i][j] - left * matrix[k + 1][j]
                             - right * matrix[k][j]) % prime
                    matrix[i][j] = matrix[j][i] = value
                    stats["elimination_updates"] += 1
            eliminated += 2
            stats["two_pivots"] += 1
        radical = interior - eliminated
        stats["max_radical"] = max(stats["max_radical"], radical)
        zero = radical >= len(keep)
        reduced = []
        if not zero:
            for row in matrix[eliminated:]:
                check()
                reduced.append(tuple(row[eliminated:]))
        check()
        return self._make(prime, keep, radical, factor, reduced, zero, stats)

    def query(self, partition, check=None):
        """Exact tree cofactor of a terminal identification, modulo prime."""
        check = _noop if check is None else check
        check()
        partition = tuple(partition)
        if (not self.terminals or len(partition) != len(self.terminals)
                or any(type(v) is not int or v < 0 for v in partition)):
            raise ValueError("partition must give one nonnegative integer per terminal")
        names, labels = {}, []
        for value in partition:
            check()
            labels.append(names.setdefault(value, len(names)))
        q, r = len(names) - 1, self.radical
        if self.zero or r > q:
            return 0
        size, prime = r + q, self.prime
        matrix = []
        for _ in range(size):
            check()
            matrix.append([0] * size)
        index = list(range(r)) + [None if v == 0 else r + v - 1 for v in labels]
        for i, left in enumerate(index):
            check()
            if left is None:
                continue
            for j, right in enumerate(index):
                check()
                if right is not None:
                    matrix[left][right] = (matrix[left][right] + self.matrix[i][j]) % prime
        value = self.factor * _determinant(matrix, prime, check) % prime
        check()
        return value


class _UnionFind:
    def __init__(self, size):
        self.parent = list(range(size))
        self.size = [1] * size

    def find(self, value):
        while value != self.parent[value]:
            self.parent[value] = self.parent[self.parent[value]]
            value = self.parent[value]
        return value

    def union(self, left, right):
        left, right = self.find(left), self.find(right)
        if left == right:
            return False
        if self.size[left] < self.size[right]:
            left, right = right, left
        self.parent[right] = left
        self.size[left] += self.size[right]
        return True


def _rot(dart):
    return (dart & -4) | ((dart + 1) & 3)


def _source(pd, order, check):
    """Check a spherical source link and return a fixed dart checkerboarding."""
    rows, pending, completed, alpha = [], {}, set(), []
    for row in pd:
        check()
        row = tuple(row)
        if len(row) != 4 or any(type(v) is not int for v in row):
            raise ValueError("crossings must have four integer edge labels")
        index = len(rows)
        rows.append(row)
        alpha.extend([-1] * 4)
        for j, label in enumerate(row):
            check()
            dart = 4 * index + j
            if label in completed:
                raise ValueError("every edge label must occur twice")
            if label in pending:
                other = pending.pop(label)
                alpha[dart], alpha[other] = other, dart
                completed.add(label)
            else:
                pending[label] = dart
    if pending:
        raise ValueError("every edge label must occur twice")
    order = tuple(order)
    if (len(order) != len(rows) or any(type(i) is not int for i in order)
            or set(order) != set(range(len(rows)))):
        raise ValueError("order must permute all crossings")
    face, count = [-1] * len(alpha), 0
    projection = _UnionFind(len(rows))
    for start in range(len(alpha)):
        check()
        projection.union(start // 4, alpha[start] // 4)
        if face[start] >= 0:
            continue
        dart = start
        while face[dart] < 0:
            check()
            face[dart] = count
            dart = _rot(alpha[dart])
        if dart != start:
            raise ValueError("invalid face permutation")
        count += 1
    roots = set()
    for crossing in range(len(rows)):
        check()
        roots.add(projection.find(crossing))
    if count != len(rows) + 2 * len(roots):
        raise ValueError("source rotation system is not spherical")
    adjacent = [set() for _ in range(count)]
    for dart, other in enumerate(alpha):
        check()
        adjacent[face[dart]].add(face[other])
    color = [-1] * count
    for start in range(count):
        check()
        if color[start] >= 0:
            continue
        color[start], queue = 0, [start]
        for current in queue:
            check()
            for neighbor in adjacent[current]:
                check()
                if color[neighbor] < 0:
                    color[neighbor] = 1 - color[current]
                    queue.append(neighbor)
                elif color[neighbor] == color[current]:
                    raise ValueError("source is not checkerboard colorable")
    return tuple(rows), order, tuple(alpha), tuple(color[f] for f in face)


class SuffixResponse:
    """One immutable suffix snapshot with checked boundary completion queries."""
    __slots__ = ("stage", "crossings", "response", "labels", "ends", "starts",
                 "colors", "projection", "closed_projection", "closed_faces",
                 "closed_black", "b_total", "anchor", "stats")

    def __setattr__(self, name, value):
        raise AttributeError("suffix snapshots are immutable")

    def __delattr__(self, name):
        raise AttributeError("suffix snapshots are immutable")

    def query(self, pairs, check=None):
        """Return a raw Jones-at-i value modulo p after checking spherical closure.

        ``value_i=(real, imaginary)`` stores the Gaussian pair formally, also
        when p=2 or -1 is a square.  Color-incompatible matchings are declined
        with ValueError.  This method never supplies a knot recognition verdict.
        """
        check = _noop if check is None else check
        check()
        pairs = tuple(tuple(pair) for pair in pairs)
        indices, seen = {label: i for i, label in enumerate(self.labels)}, set()
        for pair in pairs:
            check()
            if len(pair) != 2 or any(type(v) is not int for v in pair):
                raise ValueError("matching entries must have two integer labels")
            a, b = pair
            if a == b or a not in indices or b not in indices or a in seen or b in seen:
                raise ValueError("matching must cover the boundary exactly once")
            seen.update(pair)
        if len(seen) != len(self.labels):
            raise ValueError("matching must cover the boundary exactly once")
        roots = tuple(v for v, _ in self.colors)
        ids = {v: i for i, v in enumerate(roots)}
        colors = dict(self.colors)
        faces = _UnionFind(len(roots))
        projection_ids = {v: i for i, v in enumerate(set(self.projection))}
        projection = _UnionFind(len(projection_ids))
        for a, b in pairs:
            check()
            left, right = indices[a], indices[b]
            for end, start in ((self.ends[left], self.starts[right]),
                               (self.ends[right], self.starts[left])):
                check()
                if colors[end] != colors[start]:
                    raise ValueError("matching does not preserve inherited face colors")
                faces.union(ids[end], ids[start])
            projection.union(projection_ids[self.projection[left]],
                             projection_ids[self.projection[right]])
        face_roots, black_roots, projection_roots = set(), set(), set()
        for root in roots:
            check()
            image = faces.find(ids[root])
            face_roots.add(image)
            if colors[root]:
                black_roots.add(image)
        for i in range(len(projection_ids)):
            check()
            projection_roots.add(projection.find(i))
        shadows = self.closed_projection + len(projection_roots)
        face_count = self.closed_faces + len(face_roots)
        if face_count != self.crossings + 2 * shadows:
            raise ValueError("matching completion is not spherical")
        vertices = self.closed_black + len(black_roots)
        phase = (self.b_total + vertices - 1) % 4
        partition = []
        for terminal in self.response.terminals:
            check()
            # A closed anchor is kept separate from all open face fragments.
            partition.append(faces.find(ids[terminal]) + 1 if terminal in ids else 0)
        value = 0 if shadows != 1 else self.response.query(partition, check)
        real, imaginary = ((1, 0), (0, -1), (-1, 0), (0, 1))[phase]
        prime = self.response.prime
        check()
        return dict(value_i=(real * value % prime, imaginary * value % prime),
                    tree_mod=value, phase=phase, shadow_components=shadows,
                    partition=tuple(partition), black_vertices=vertices)


def iter_suffix_responses(pd, order=None, prime=65521, check=None, *, max_boundary=None):
    """Yield all nonempty suffixes in reverse stage order, sharing elimination.

    Storage retained by this iterator is O(n+(W+1)**2); retaining yielded
    snapshots adds O(n*(W+1)**2).  Source validation is also interruptible.
    A completed immutable snapshot is the only value ever yielded.  An optional
    max_boundary cap stops before building a response whose frontier exceeds
    that cap; previous yielded snapshots remain valid.
    """
    check = _noop if check is None else check
    check()
    _allowance(max_boundary, "max_boundary")
    pd = tuple(tuple(row) for row in pd)
    order = tuple(range(len(pd))) if order is None else tuple(order)
    pd, order, alpha, palette = _source(pd, order, check)
    response = StreamingResponse.empty(prime, check)
    n = len(pd)
    faces, projection = _UnionFind(4 * n), _UnionFind(n)
    active, boundary = bytearray(n), {}
    total_faces = black_faces = projection_components = b_total = 0
    anchor = None
    max_seen_boundary = max_live = geometry_visits = 0
    for stage in range(n - 1, -1, -1):
        check()
        crossing = order[stage]
        active[crossing] = 1
        total_faces += 4
        black_faces += 2
        projection_components += 1
        darts = tuple(range(4 * crossing, 4 * crossing + 4))
        added = tuple(d for d in darts if palette[d])
        if len(added) != 2 or added[1] - added[0] != 2:
            raise ArithmeticError("checkerboard sectors fail to alternate")
        if anchor is None:
            anchor = added[0]
        live_black = set(response.terminals) | set(added)
        for dart in darts:
            check()
            geometry_visits += 1
            label = pd[crossing][dart % 4]
            if label in boundary:
                boundary.pop(label)
            else:
                boundary[label] = dart
        for dart in darts:
            check()
            other = alpha[dart]
            if not active[other // 4] or (other // 4 == crossing and dart > other):
                continue
            projection_components -= int(projection.union(crossing, other // 4))
            for first, second in ((dart, _rot(other)), (other, _rot(dart))):
                check()
                geometry_visits += 1
                left, right = faces.find(first), faces.find(second)
                if palette[left] != palette[right]:
                    raise ArithmeticError("internal face connection changes color")
                if left == right:
                    continue
                if palette[left]:
                    if left not in live_black or right not in live_black:
                        raise ArithmeticError("a closed interior face was identified")
                    live_black.remove(left)
                    live_black.remove(right)
                faces.union(left, right)
                total_faces -= 1
                if palette[left]:
                    black_faces -= 1
                    live_black.add(faces.find(left))
        check()
        labels = tuple(sorted(boundary))
        if max_boundary is not None and len(labels) > max_boundary:
            raise ResponseBudget("suffix frontier allowance exhausted")
        ends, starts, open_faces, open_black, projection_labels = [], [], set(), set(), []
        for label in labels:
            check()
            geometry_visits += 1
            dart = boundary[label]
            end, start = faces.find(dart), faces.find(_rot(dart))
            ends.append(end)
            starts.append(start)
            open_faces.update((end, start))
            if palette[end]:
                open_black.add(end)
            if palette[start]:
                open_black.add(start)
            projection_labels.append(projection.find(dart // 4))
        anchor = faces.find(anchor)
        keep = tuple(sorted(open_black | {anchor}))
        identifications = {}
        for vertex in response.terminals + added:
            check()
            identifications[vertex] = faces.find(vertex)
        b = int(added[0] % 4 == 0)
        b_total += b
        response = response.advance(added, ((added[0], added[1], -1 if b else 1),),
                                    identifications, keep, check)
        max_seen_boundary = max(max_seen_boundary, len(labels))
        max_live = max(max_live, len(keep))
        colors = []
        for root in sorted(open_faces):
            check()
            colors.append((root, palette[root]))
        stats = dict(response.stats, max_boundary=max_seen_boundary,
                     max_retained_terminals=max_live, geometry_visits=geometry_visits)
        snapshot = SuffixResponse()
        values = (stage, n - stage, response, labels, tuple(ends), tuple(starts),
                  tuple(colors), tuple(projection_labels),
                  projection_components - len(set(projection_labels)),
                  total_faces - len(open_faces), black_faces - len(open_black),
                  b_total, anchor, tuple(sorted(stats.items())))
        for name, value in zip(SuffixResponse.__slots__, values):
            object.__setattr__(snapshot, name, value)
        check()
        yield snapshot


def compile_suffix_responses(pd, order=None, prime=65521, check=None, *,
                             max_boundary=None, max_stored_elements=None):
    """Return immutable suffix snapshots indexed by their prefix stage.

    max_stored_elements caps the sum of squared retained response dimensions.
    It is checked before each completed snapshot is retained; it does not count
    geometric metadata or the current update's transient working matrix.
    Exhaustion raises ResponseBudget and returns no partial compiled tuple.
    """
    _allowance(max_stored_elements, "max_stored_elements")
    result, stored = [], 0
    for snapshot in iter_suffix_responses(pd, order, prime, check, max_boundary=max_boundary):
        stored += len(snapshot.response.matrix) ** 2
        if max_stored_elements is not None and stored > max_stored_elements:
            raise ResponseBudget("retained field-element allowance exhausted")
        result.append(snapshot)
    result.reverse()
    return tuple(result)
