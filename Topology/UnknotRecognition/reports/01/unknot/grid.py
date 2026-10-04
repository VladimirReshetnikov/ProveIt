"""Unoriented rectangular knot diagrams and Dynnikov's non-increasing moves.

Rows run bottom-to-top; columns run left-to-right. Vertical segments pass OVER
horizontal segments. The represented object is an ordinary link in S^3, not a
virtual link. Cyclic shifts of all rows or columns are regarded as equivalences.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterator, Sequence


class DiagramError(ValueError):
    """Malformed diagram or move."""


def _integer(value: Any, name: str) -> int:
    if type(value) is not int:  # Reject bool and accidental floating-point input.
        raise DiagramError(f"{name} must be an integer")
    return value


def _least_rotation(sequence: tuple[tuple[int, int], ...]) -> int:
    """Booth's algorithm: an index of the lexicographically least rotation."""
    n = len(sequence)
    doubled = sequence + sequence
    i, j, k = 0, 1, 0
    while i < n and j < n and k < n:
        a, b = doubled[i + k], doubled[j + k]
        if a == b:
            k += 1
        elif a > b:
            i += k + 1
            if i <= j:
                i = j + 1
            k = 0
        else:
            j += k + 1
            if j <= i:
                j = i + 1
            k = 0
    return min(i, j)


@dataclass(frozen=True)
class Grid:
    """Two distinct marked corners per row and per column.

    Construct through from_rows/from_json at an untrusted input boundary. The
    direct constructor also validates: there is deliberately no unsafe fast path.
    """

    rows: tuple[tuple[int, int], ...]

    def __post_init__(self) -> None:
        if not isinstance(self.rows, tuple) or len(self.rows) < 2:
            raise DiagramError("a grid needs at least two rows")
        n = len(self.rows)
        counts = [0] * n
        for row in self.rows:
            if not isinstance(row, tuple) or len(row) != 2:
                raise DiagramError("each row must contain two columns")
            a, b = row
            if type(a) is not int or type(b) is not int or not 0 <= a < b < n:
                raise DiagramError("row endpoints must satisfy 0 <= a < b < size")
            counts[a] += 1
            counts[b] += 1
        if any(count != 2 for count in counts):
            raise DiagramError("every column must contain exactly two corners")

    @classmethod
    def from_rows(cls, rows: Sequence[Sequence[int]]) -> Grid:
        if not isinstance(rows, (list, tuple)):
            raise DiagramError("rows must be an array")
        result = []
        for row in rows:
            if not isinstance(row, (list, tuple)) or len(row) != 2:
                raise DiagramError("each row must contain two columns")
            a, b = (_integer(x, "column") for x in row)
            result.append(tuple(sorted((a, b))))
        return cls(tuple(result))

    @classmethod
    def from_json(cls, value: Any) -> Grid:
        if not isinstance(value, dict):
            raise DiagramError("diagram must be a JSON object")
        if "rows" in value and "x" not in value and "o" not in value:
            return cls.from_rows(value["rows"])
        if "x" in value and "o" in value and "rows" not in value:
            x, o = value["x"], value["o"]
            if not isinstance(x, list) or not isinstance(o, list) or len(x) != len(o):
                raise DiagramError("x and o must be equal-length arrays")
            n = len(x)
            for permutation in (x, o):
                if any(type(a) is not int for a in permutation):
                    raise DiagramError("x and o must contain integers")
                if sorted(permutation) != list(range(n)):
                    raise DiagramError("x and o must each be a permutation of 0..size-1")
            return cls.from_rows(list(zip(x, o)))
        raise DiagramError("supply either rows, or x and o (columns indexed by row)")

    @property
    def size(self) -> int:
        return len(self.rows)

    def to_json(self) -> dict[str, Any]:
        return {"rows": [list(row) for row in self.rows]}

    def columns(self) -> tuple[tuple[int, int], ...]:
        columns: list[list[int]] = [[] for _ in self.rows]
        for r, row in enumerate(self.rows):
            for c in row:
                columns[c].append(r)
        return tuple((column[0], column[1]) for column in columns)

    def components(self) -> int:
        """Connected components of the degree-two corner incidence graph."""
        columns = self.columns()
        unseen = set(range(self.size))
        count = 0
        while unseen:
            count += 1
            stack = [unseen.pop()]
            while stack:
                r = stack.pop()
                for c in self.rows[r]:
                    for s in columns[c]:
                        if s in unseen:
                            unseen.remove(s)
                            stack.append(s)
        return count

    def shift(self, row_shift: int, column_shift: int) -> Grid:
        n = self.size
        return Grid(tuple(
            tuple(sorted((c + column_shift) % n for c in self.rows[(r + row_shift) % n]))
            for r in range(n)
        ))

    def canonical(self) -> Grid:
        """Quotient only by cyclic shifts, not by arbitrary row permutations.

        O(size^2) small-integer operations; no global cache or hidden state.
        """
        n = self.size
        best = self.rows
        for dc in range(n):
            shifted = tuple(tuple(sorted(((a + dc) % n, (b + dc) % n)))
                            for a, b in self.rows)
            k = _least_rotation(shifted)
            candidate = shifted[k:] + shifted[:k]
            if candidate < best:
                best = candidate
        return self if best == self.rows else Grid(best)

    def crossing_count(self) -> int:
        columns = self.columns()
        return sum(columns[c][0] < r < columns[c][1]
                   for r, (a, b) in enumerate(self.rows) for c in range(a + 1, b))

    def events(self) -> tuple[tuple[tuple[int, int], bool], ...]:
        """One oriented traversal, (crossing=(row,column), is_over) events.

        Starting orientation is arbitrary. Requires a single knot component.
        """
        if self.components() != 1:
            raise DiagramError("this operation requires a single knot component")
        columns = self.columns()
        start = (0, self.rows[0][0])
        r, c = start
        events = []
        while True:
            a, b = self.rows[r]
            d = b if c == a else a
            step = 1 if d > c else -1
            for col in range(c + step, d, step):
                lo, hi = columns[col]
                if lo < r < hi:
                    events.append(((r, col), False))
            c = d
            lo, hi = columns[c]
            s = hi if r == lo else lo
            step = 1 if s > r else -1
            for row in range(r + step, s, step):
                a, b = self.rows[row]
                if a < c < b:
                    events.append(((row, c), True))
            r = s
            if (r, c) == start:
                return tuple(events)

    def ascii(self) -> str:
        n = self.size
        columns = self.columns()
        lines = []
        for r in reversed(range(n)):
            a, b = self.rows[r]
            line = []
            for c in range(n):
                lo, hi = columns[c]
                if c in self.rows[r]:
                    line.append("o")
                elif lo < r < hi:
                    line.append("|")
                elif a < c < b:
                    line.append("-")
                else:
                    line.append(" ")
                if c < n - 1:
                    line.append("-" if a <= c < b else " ")
            lines.append("".join(line).rstrip())
        return "\n".join(lines)


def exchangeable(first: tuple[int, int], second: tuple[int, int]) -> bool:
    """Dynnikov exchange: disjoint endpoint sets, non-alternating cyclic order."""
    a, b = first
    c, d = second
    return (len({a, b, c, d}) == 4
            and not (a < c < b < d or c < a < d < b))


@dataclass(frozen=True)
class Move:
    kind: str
    index: int
    column: int | None = None

    @classmethod
    def from_json(cls, value: Any) -> Move:
        if not isinstance(value, dict) or not isinstance(value.get("kind"), str):
            raise DiagramError("move must contain a string kind")
        kind = value["kind"]
        index = _integer(value.get("index"), "move index")
        column = value.get("column")
        if kind == "destabilize":
            column = _integer(column, "destabilization column")
        elif column is not None:
            raise DiagramError("only destabilization takes a column")
        if kind not in {"row_exchange", "column_exchange", "destabilize"}:
            raise DiagramError("unknown move kind")
        return cls(kind, index, column)

    def to_json(self) -> dict[str, Any]:
        result: dict[str, Any] = {"kind": self.kind, "index": self.index}
        if self.column is not None:
            result["column"] = self.column
        return result

    def apply(self, grid: Grid) -> Grid:
        """Apply a fully checked move. Does NOT canonicalize its result."""
        n = grid.size
        i = self.index
        if type(i) is not int or not 0 <= i < n:
            raise DiagramError("move index is out of range")
        j = (i + 1) % n
        if self.kind == "row_exchange":
            if self.column is not None or not exchangeable(grid.rows[i], grid.rows[j]):
                raise DiagramError("rows cannot be exchanged")
            rows = list(grid.rows)
            rows[i], rows[j] = rows[j], rows[i]
            return Grid(tuple(rows))
        if self.kind == "column_exchange":
            columns = grid.columns()
            if self.column is not None or not exchangeable(columns[i], columns[j]):
                raise DiagramError("columns cannot be exchanged")
            return Grid(tuple(tuple(sorted(j if c == i else i if c == j else c
                                          for c in row)) for row in grid.rows))
        if self.kind != "destabilize":
            raise DiagramError("unknown move kind")
        c = self.column
        if n <= 2 or type(c) is not int or c not in grid.rows[i]:
            raise DiagramError("invalid destabilization corner")
        a, b = grid.rows[i]
        d = b if c == a else a
        lo, hi = grid.columns()[c]
        s = hi if i == lo else lo
        if ((d - c) % n not in {1, n - 1}
                or (s - i) % n not in {1, n - 1} or d in grid.rows[s]):
            raise DiagramError("destabilization requires three corners of an empty 2x2 block")
        rows = []
        for r, row in enumerate(grid.rows):
            if r == i:
                continue
            values = [d if r == s and x == c else x for x in row]
            rows.append(tuple(sorted(x - (x > c) for x in values)))
        return Grid(tuple(rows))


def moves(grid: Grid) -> Iterator[Move]:
    """All elementary non-increasing moves, including cyclic neighbors."""
    n = grid.size
    columns = grid.columns()
    if n > 2:
        for r, row in enumerate(grid.rows):
            for c in row:
                d = row[1] if c == row[0] else row[0]
                lo, hi = columns[c]
                s = hi if r == lo else lo
                if ((d - c) % n in {1, n - 1}
                        and (s - r) % n in {1, n - 1} and d not in grid.rows[s]):
                    yield Move("destabilize", r, c)
    for i in range(n):
        j = (i + 1) % n
        if exchangeable(grid.rows[i], grid.rows[j]):
            yield Move("row_exchange", i)
        if exchangeable(columns[i], columns[j]):
            yield Move("column_exchange", i)


def successors(grid: Grid) -> Iterator[tuple[Grid, Move]]:
    seen = {grid}
    for move in moves(grid):
        child = move.apply(grid).canonical()
        if child not in seen:
            seen.add(child)
            yield child, move
