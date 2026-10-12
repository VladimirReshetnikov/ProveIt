"""Exact suffix path summaries for classical completion Euler queries.

The strand and all-zero-smoothing graphs are unions of paths and circles.
Prepare their boundary pairings once. Each subsequent completion counts cycles
in two boundary matching overlays without revisiting the suffix crossings.
"""


class BoundaryConnectivity:
    def __init__(self, alpha, boundary, check=lambda: None):
        self.crossings = len(alpha) // 4
        self.labels = tuple(sorted(boundary))
        self.index = {label: i for i, label in enumerate(self.labels)}
        darts = tuple(boundary[label] for label in self.labels)
        self.strands, self.strand_circles = self._paths(alpha, darts, 2, check)
        self.zero, self.zero_circles = self._paths(alpha, darts, 1, check)

    @staticmethod
    def _paths(alpha, darts, switch, check):
        ids = {dart: i for i, dart in enumerate(darts)}
        seen = bytearray(len(alpha))
        pairing = [-1] * len(darts)
        for i, start in enumerate(darts):
            check()
            if seen[start]:
                continue
            dart = start
            while True:
                check()
                if seen[dart] or seen[dart ^ switch]:
                    raise ArithmeticError("suffix path repeats a visited dart")
                other = dart ^ switch
                seen[dart] = seen[other] = 1
                nxt = alpha[other]
                if nxt < 0:
                    j = ids[other]
                    pairing[i], pairing[j] = j, i
                    break
                dart = nxt
        circles = 0
        for start in range(len(alpha)):
            if seen[start]:
                continue
            circles += 1
            dart = start
            while not seen[dart]:
                check()
                other = dart ^ switch
                seen[dart] = seen[other] = 1
                dart = alpha[other]
                if dart < 0:
                    raise ArithmeticError("unvisited open suffix path")
            if dart != start:
                raise ArithmeticError("suffix circle does not close")
        if -1 in pairing:
            raise ArithmeticError("suffix paths do not pair the boundary")
        return tuple(pairing), circles

    @staticmethod
    def _cycles(paths, closure, check):
        seen = bytearray(len(paths))
        count = 0
        for start in range(len(paths)):
            if seen[start]:
                continue
            count += 1
            dart = start
            while not seen[dart]:
                check()
                other = paths[dart]
                seen[dart] = seen[other] = 1
                dart = closure[other]
            if dart != start:
                raise ArithmeticError("boundary overlay does not close")
        return count

    def counts(self, pairs, check=lambda: None):
        """Return (link components, all-zero circles) of an actual completion.

        Empty suffix plus empty matching represents the scalar terminal value,
        with both counts zero, not an implicit crossingless circle.
        """
        closure = [-1] * len(self.labels)
        for left, right in pairs:
            check()
            a, b = self.index.get(left), self.index.get(right)
            if a is None or b is None or a == b or closure[a] >= 0 or closure[b] >= 0:
                raise ValueError("matching does not pair the suffix frontier")
            closure[a], closure[b] = b, a
        if -1 in closure:
            raise ValueError("matching does not cover the suffix frontier")
        return (self.strand_circles + self._cycles(self.strands, closure, check),
                self.zero_circles + self._cycles(self.zero, closure, check))

    def euler(self, pairs, check=lambda: None):
        components, zero_circles = self.counts(pairs, check)
        # The oriented Seifert state has s circles, s == n+c mod 2.
        # Changing its h oriented-one smoothings from state zero gives
        # s == c0+h mod 2, hence h == n+c+c0 mod 2.
        sign = -1 if (self.crossings + components + zero_circles) % 2 else 1
        return sign * (1 << components)
