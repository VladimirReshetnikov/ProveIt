"""Exact two-flow bijections for bipartite demand polytopes.

Python 3.10+, standard library only. All optimizer and certificate arithmetic
is integral. No enumeration of a triangulation or of bases is used by either
map. Exhaustive enumeration is isolated in the separate verify.py module.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from heapq import heappop, heappush
from random import Random
from typing import Iterable, Sequence


@dataclass
class _Edge:
    to: int
    rev: int
    cap: int
    cost: int


@dataclass(frozen=True)
class Certificate:
    """A primal tree flow and independently checkable optimality potentials."""
    support: tuple[int, ...]
    row_margins: tuple[int, ...]
    column_margins: tuple[int, ...]  # dummy 0 first; then support order
    flow: tuple[tuple[int, int, int], ...]  # x, y (-1 for dummy), amount
    row_potentials: tuple[int, ...]
    column_potentials: tuple[int, ...]
    augmentations: int


@dataclass(frozen=True)
class CoreCertificate:
    """Selected-row transport and independent attachments of all other rows."""
    suppliers: tuple[int, ...]
    transport: Certificate  # supplier indices are positions in suppliers
    attachments: tuple[tuple[int, int], ...]  # original x, chosen y


class BipartiteDemand:
    """Suppliers 0..m-1; receivers 0..n-1; dummy receiver is -1.

    edge_order optionally fixes a cycle-generic integer cost system. It must
    list every augmented edge exactly once. Restricting receiver sets keeps
    these same costs; rebuilding with a different order can change the map.
    """
    def __init__(self, m: int, n: int, edges: Iterable[tuple[int, int]],
                 edge_order: Sequence[tuple[int, int]] | None = None):
        if not isinstance(m, int) or not isinstance(n, int) or m < 0 or n < 0:
            raise ValueError("m and n must be nonnegative integers")
        self.m, self.n = m, n
        self.edges = frozenset(edges)
        if any(not (isinstance(x, int) and isinstance(y, int)
                    and 0 <= x < m and 0 <= y < n) for x, y in self.edges):
            raise ValueError("edge endpoint outside the declared graph")
        augmented = self.edges | {(x, -1) for x in range(m)}
        order = list(sorted(augmented) if edge_order is None else edge_order)
        if len(order) != len(augmented) or set(order) != augmented:
            raise ValueError("edge_order must list all augmented edges once")
        self.cost = {edge: 1 << i for i, edge in enumerate(order)}
        neighbors = [set() for _ in range(n)]
        targets = [set() for _ in range(m)]
        for x, y in self.edges:
            neighbors[y].add(x)
            targets[x].add(y)
        self.neighbors = tuple(frozenset(a) for a in neighbors)
        self.targets = tuple(frozenset(a) for a in targets)

    def _set(self, values: Iterable[int], bound: int, name: str) -> tuple[int, ...]:
        value_list = list(values)
        if any(not isinstance(v, int) or not 0 <= v < bound for v in value_list):
            raise ValueError(f"invalid {name}")
        if len(set(value_list)) != len(value_list):
            raise ValueError(f"duplicate in {name}")
        return tuple(sorted(value_list))

    @staticmethod
    def _saturates(neighborhoods: Sequence[Iterable[int]]) -> bool:
        """Iterative augmenting paths; no Python recursion-depth dependence."""
        owner: dict[int, int] = {}
        assigned: dict[int, int] = {}
        for initial in range(len(neighborhoods)):
            queue = deque([initial])
            visited = {initial}
            predecessor: dict[int, int] = {}
            free = None
            while queue and free is None:
                y = queue.popleft()
                for x in sorted(neighborhoods[y]):
                    if x in predecessor:
                        continue
                    predecessor[x] = y
                    if x not in owner:
                        free = x
                        break
                    previous = owner[x]
                    if previous not in visited:
                        visited.add(previous)
                        queue.append(previous)
            if free is None:
                return False
            x = free
            while True:
                y = predecessor[x]
                old = assigned.get(y)
                owner[x] = y
                assigned[y] = x
                if old is None:
                    break
                x = old
        return True

    def matchable(self, suppliers: Iterable[int], receivers: Iterable[int]) -> bool:
        """Augmenting-path bipartite matching; no perfect matching counting."""
        I = self._set(suppliers, self.m, "supplier set")
        J = self._set(receivers, self.n, "receiver set")
        if len(I) != len(J):
            return False
        allowed = set(I)
        return self._saturates([self.neighbors[y] & allowed for y in J])

    def is_demand(self, c: Sequence[int]) -> bool:
        """Polynomial Hall test by expanding at most m demanded copies."""
        if len(c) != self.n or any(not isinstance(v, int) or v < 0 for v in c):
            return False
        if sum(c) > self.m:
            return False
        return self._saturates([self.neighbors[y] for y, value in enumerate(c)
                               for _ in range(value)])

    def _transport(self, J: tuple[int, ...], rows: Sequence[int],
                   cols: Sequence[int]) -> Certificate:
        """Successive shortest augmenting paths, integral reduced costs."""
        m, k = self.m, len(J) + 1
        if len(rows) != m or len(cols) != k or sum(rows) != sum(cols):
            raise ValueError("inconsistent transportation margins")
        if any(v <= 0 for v in (*rows, *cols)):
            raise ValueError("the nonempty-support algorithms need positive margins")
        N, source, sink = m + k + 2, m + k, m + k + 1
        graph: list[list[_Edge]] = [[] for _ in range(N)]
        def add(a: int, b: int, cap: int, cost: int) -> int:
            index = len(graph[a])
            graph[a].append(_Edge(b, len(graph[b]), cap, cost))
            graph[b].append(_Edge(a, index, 0, -cost))
            return index
        target = sum(rows)
        for x, value in enumerate(rows):
            add(source, x, value, 0)
        for j, value in enumerate(cols):
            add(m+j, sink, value, 0)
        refs = []
        for x in range(m):
            for j, y in enumerate((-1,) + J):
                if (x, y) in self.cost:
                    idx = add(x, m+j, target, self.cost[x, y])
                    refs.append((x, y, idx))
        potential = [0] * N
        sent = augmentations = 0
        while sent < target:
            distance: list[int | None] = [None] * N
            parent: list[tuple[int, int] | None] = [None] * N
            distance[source] = 0
            queue = [(0, source)]
            while queue:
                d, a = heappop(queue)
                if d != distance[a]:
                    continue
                for i, e in enumerate(graph[a]):
                    if e.cap == 0:
                        continue
                    reduced = e.cost + potential[a] - potential[e.to]
                    if reduced < 0:
                        raise RuntimeError("invalid reduced-cost invariant")
                    nd = d + reduced
                    if distance[e.to] is None or nd < distance[e.to]:
                        distance[e.to] = nd
                        parent[e.to] = (a, i)
                        heappush(queue, (nd, e.to))
            if distance[sink] is None:
                raise ValueError("infeasible transportation problem")
            for a, d in enumerate(distance):
                if d is not None:
                    potential[a] += d
            amount, v = target - sent, sink
            while v != source:
                step = parent[v]
                if step is None:
                    raise RuntimeError("missing augmenting path")
                a, i = step
                amount = min(amount, graph[a][i].cap)
                v = a
            v = sink
            while v != source:
                a, i = parent[v]  # type: ignore[misc]
                e = graph[a][i]
                e.cap -= amount
                graph[v][e.rev].cap += amount
                v = a
            sent += amount
            augmentations += 1
        flow = tuple((x, y, target-graph[x][idx].cap)
                     for x, y, idx in refs if target-graph[x][idx].cap > 0)
        # Derive the dual potentials afresh from the support tree, rather
        # than trusting optimizer potentials with source/sink arcs.
        column_index = {y: j for j, y in enumerate((-1,) + J)}
        tree: list[list[tuple[int, int]]] = [[] for _ in range(m+k)]
        for x, y, _ in flow:
            v = m + column_index[y]
            w = self.cost[x, y]
            tree[x].append((v, w)); tree[v].append((x, w))
        dual: list[int | None] = [None] * (m+k)
        dual[m] = 0
        stack = [m]
        while stack:
            a = stack.pop()
            for b, w in tree[a]:
                candidate = w - dual[a]  # type: ignore[operator]
                if dual[b] is None:
                    dual[b] = candidate; stack.append(b)
                elif dual[b] != candidate:
                    raise RuntimeError("support is not dual-consistent")
        if any(v is None for v in dual):
            raise RuntimeError("support is not connected")
        cert = Certificate(J, tuple(rows), tuple(cols), flow,
                           tuple(dual[:m]), tuple(dual[m:]), augmentations)  # type: ignore[arg-type]
        self.verify_certificate(cert)
        return cert

    def verify_certificate(self, cert: Certificate) -> None:
        """Independent linear-sized primal/dual optimality checker."""
        J = self._set(cert.support, self.n, "certificate support")
        m, k = self.m, len(J)+1
        if J != cert.support or len(cert.row_margins) != m or len(cert.column_margins) != k:
            raise ValueError("bad certificate dimensions")
        if len(cert.row_potentials) != m or len(cert.column_potentials) != k:
            raise ValueError("bad potential dimensions")
        col_index = {y: j for j, y in enumerate((-1,) + J)}
        rows, cols = [0]*m, [0]*k
        parent = list(range(m+k))
        def root(a: int) -> int:
            while parent[a] != a:
                parent[a] = parent[parent[a]]; a = parent[a]
            return a
        seen = set()
        for x, y, amount in cert.flow:
            if (x, y) not in self.cost or y not in col_index or amount <= 0:
                raise ValueError("illegal positive-flow edge")
            if not isinstance(amount, int) or (x, y) in seen:
                raise ValueError("nonintegral flow or duplicate edge")
            seen.add((x, y)); j = col_index[y]
            rows[x] += amount; cols[j] += amount
            if cert.row_potentials[x]+cert.column_potentials[j] != self.cost[x, y]:
                raise ValueError("nonzero reduced cost on a tree edge")
            a, b = root(x), root(m+j)
            if a == b:
                raise ValueError("cycle in positive-flow support")
            parent[a] = b
        if len(seen) != m+k-1 or len({root(a) for a in range(m+k)}) != 1:
            raise ValueError("support is not a spanning tree")
        if tuple(rows) != cert.row_margins or tuple(cols) != cert.column_margins:
            raise ValueError("wrong margins")
        for (x, y), cost in self.cost.items():
            if y in col_index:
                slack = cost-cert.row_potentials[x]-cert.column_potentials[col_index[y]]
                if slack < 0 or ((x, y) not in seen and slack == 0):
                    raise ValueError("invalid strict optimality certificate")

    def basis_to_demand(self, suppliers: Iterable[int], receivers: Iterable[int],
                        *, certificate: bool = False):
        I = self._set(suppliers, self.m, "supplier set")
        J = self._set(receivers, self.n, "receiver set")
        if not self.matchable(I, J):
            raise ValueError("the support pair is not matchable")
        if not J:
            answer = (0,)*self.n
            return (answer, None) if certificate else answer
        Iset, m, r = set(I), self.m, len(J)
        cert = self._transport(J, [m*int(x in Iset)+1 for x in range(m)],
                               [m]*(r+1))
        adjacency = [[] for _ in range(m)]
        for x, y, _ in cert.flow:
            adjacency[x].append(y)
        if any(len(adjacency[x]) != 1+int(x in Iset) for x in range(m)):
            raise RuntimeError("incorrect supplier degree pattern")
        c = [int(y in J) for y in range(self.n)]
        for x in range(m):
            if x not in Iset and adjacency[x][0] != -1:
                c[adjacency[x][0]] += 1
        answer = tuple(c)
        return (answer, cert) if certificate else answer

    def _core_graph(self, I: tuple[int, ...]) -> BipartiteDemand:
        index = {x: i for i, x in enumerate(I)}
        G = BipartiteDemand(len(I), self.n,
                            ((index[x], y) for x, y in self.edges if x in index))
        # Preserve the original cost system rather than choose a new order.
        G.cost = {(index[x], y): w for (x, y), w in self.cost.items() if x in index}
        return G

    def basis_to_demand_core(self, suppliers: Iterable[int], receivers: Iterable[int],
                             *, certificate: bool = False):
        """Faster forward map: flow only on the selected r suppliers.

        Its total flow is r*(r+1), followed by one reduced-cost minimization
        for every unselected supplier. It equals basis_to_demand exactly.
        """
        I = self._set(suppliers, self.m, "supplier set")
        J = self._set(receivers, self.n, "receiver set")
        if not self.matchable(I, J):
            raise ValueError("the support pair is not matchable")
        if not J:
            answer = (0,)*self.n
            return (answer, None) if certificate else answer
        r = len(J)
        Iset, Jset = set(I), set(J)
        G = self._core_graph(I)
        transport = G._transport(J, [r+1]*r, [r]*(r+1))
        v = dict(zip((-1,)+J, transport.column_potentials))
        c = [int(y in J) for y in range(self.n)]
        attachments = []
        for x in range(self.m):
            if x in Iset:
                continue
            available = (self.targets[x] & Jset) | {-1}
            scores = [(self.cost[x,y]-v[y], y) for y in available]
            best, y = min(scores)
            if sum(score == best for score, _ in scores) != 1:
                raise RuntimeError("cost system is not cycle-generic")
            attachments.append((x,y))
            if y != -1:
                c[y] += 1
        answer = tuple(c)
        cert = CoreCertificate(I, transport, tuple(attachments))
        self.verify_core_certificate(answer, cert)
        return (answer, cert) if certificate else answer

    def verify_core_certificate(self, c: Sequence[int], cert: CoreCertificate) -> None:
        """Check the small core flow and every independent leaf choice."""
        I = self._set(cert.suppliers, self.m, "core suppliers")
        J = self._set(cert.transport.support, self.n, "core receivers")
        if not J or len(I) != len(J):
            raise ValueError("a nonempty balanced core is required")
        r = len(J)
        G = self._core_graph(I)
        G.verify_certificate(cert.transport)
        if cert.transport.row_margins != (r+1,)*r or cert.transport.column_margins != (r,)*(r+1):
            raise ValueError("wrong core margins")
        v = dict(zip((-1,)+J, cert.transport.column_potentials))
        if tuple(x for x,y in cert.attachments) != tuple(x for x in range(self.m) if x not in I):
            raise ValueError("wrong set or order of supplier attachments")
        decoded = [int(y in J) for y in range(self.n)]
        for x,y in cert.attachments:
            if y not in v or (x,y) not in self.cost:
                raise ValueError("invalid leaf attachment")
            chosen = self.cost[x,y]-v[y]
            available = (self.targets[x] & set(J)) | {-1}
            if any(self.cost[x,z]-v[z] <= chosen for z in available if z != y):
                raise ValueError("attachment is not the unique reduced-cost minimum")
            if y != -1:
                decoded[y] += 1
        if tuple(decoded) != tuple(c):
            raise ValueError("wrong decoded vector")

    def demand_to_basis(self, c: Sequence[int], *, certificate: bool = False):
        if len(c) != self.n or any(not isinstance(v, int) or v < 0 for v in c):
            raise ValueError("demand must be a nonnegative integer vector")
        if sum(c) > self.m:
            raise ValueError("total demand exceeds the number of suppliers")
        J = tuple(y for y, v in enumerate(c) if v)
        if not J:
            answer = ((), ())
            return (answer, None) if certificate else answer
        r, L = len(J), len(J)+1
        cert = self._transport(J, [L]*self.m,
                               [L*(self.m-sum(c))+r]+[L*c[y]-1 for y in J])
        degrees = [0]*self.m
        for x, _, _ in cert.flow:
            degrees[x] += 1
        if any(d not in (1, 2) for d in degrees):
            raise RuntimeError("demand-flow supplier has degree above two")
        I = tuple(x for x, d in enumerate(degrees) if d == 2)
        if len(I) != r:
            raise RuntimeError("incorrect recovered matching rank")
        answer = (I, J)
        return (answer, cert) if certificate else answer

    def is_lifted_basis(self, B: Iterable[int]) -> bool:
        Bset = set(B)
        if len(Bset) != self.m or any(not 0 <= b < self.m+self.n for b in Bset):
            return False
        I = tuple(x for x in range(self.m) if x not in Bset)
        J = tuple(y for y in range(self.n) if self.m+y in Bset)
        return self.matchable(I, J)

    def decode_lifted_basis(self, B: Iterable[int]) -> tuple[int, ...]:
        Bset = set(B)
        if not self.is_lifted_basis(Bset):
            raise ValueError("invalid basis of the lifted transversal matroid")
        return self.basis_to_demand_core((x for x in range(self.m) if x not in Bset),
                                        (y for y in range(self.n) if self.m+y in Bset))

    def sample_demand(self, epsilon: float, *, rng: Random | None = None,
                      support_weights: Sequence[int] | None = None,
                      steps: int | None = None) -> tuple[int, ...]:
        """Almost-uniform full demand vector via the matroid down-up walk.

        Positive INTEGER support weights give exact discrete transitions.
        A user-supplied steps overrides the conservative theoretical budget;
        the epsilon guarantee then applies only if that budget is met.
        This basic implementation favors clarity over speed.
        """
        if not 0 < epsilon < 1:
            raise ValueError("epsilon must lie strictly between 0 and 1")
        rng = Random() if rng is None else rng
        weights_y = [1]*self.n if support_weights is None else list(support_weights)
        if len(weights_y) != self.n or any(not isinstance(w, int) or w <= 0 for w in weights_y):
            raise ValueError("support weights must be positive integers")
        if self.m == 0:
            return (0,)*self.n
        weights = [1]*self.m + weights_y
        N = self.m+self.n
        # Integer upper bound for the logarithmic mixing budget: log(z)
        # <= ceil(log2(z)) for z >= 1. No rounded logarithms are needed.
        eps_num, eps_den = epsilon.as_integer_ratio()
        bits_epsilon = max(0, eps_den.bit_length()-eps_num.bit_length())
        if eps_num << bits_epsilon < eps_den:
            bits_epsilon += 1
        bits_weight = (max(weights)-1).bit_length()
        budget = self.m*(N+self.m*bits_weight+2*bits_epsilon+2)
        if steps is None:
            steps = budget
        if not isinstance(steps, int) or steps < 0:
            raise ValueError("steps must be a nonnegative integer")
        B = set(range(self.m))
        for _ in range(steps):
            removed = rng.choice(sorted(B)); B.remove(removed)
            candidates = [e for e in range(N) if e not in B and self.is_lifted_basis(B | {e})]
            total = sum(weights[e] for e in candidates)
            ticket = rng.randrange(total)
            for e in candidates:
                ticket -= weights[e]
                if ticket < 0:
                    B.add(e); break
        return self.decode_lifted_basis(B)


def preorder_graph(rows: Sequence[Iterable[int]]) -> BipartiteDemand:
    """rows[x] contains all y satisfying x <= y; validate the preorder."""
    n = len(rows)
    sets = [set(row) for row in rows]
    if any(any(not isinstance(y, int) or not 0 <= y < n for y in row) for row in sets):
        raise ValueError("invalid preorder endpoint")
    if any(x not in sets[x] for x in range(n)):
        raise ValueError("the relation is not reflexive")
    if any(not sets[y] <= sets[x] for x in range(n) for y in sets[x]):
        raise ValueError("the relation is not transitive")
    return BipartiteDemand(n, n, ((x, y) for x in range(n) for y in sets[x]))


if __name__ == '__main__':
    H = BipartiteDemand(4, 3, [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2), (3, 2)])
    I, J = (0, 1, 3), (0, 1, 2)
    c, cert = H.basis_to_demand(I, J, certificate=True)
    print('support pair:', (I, J))
    print('demand vector:', c)
    print('inverse:', H.demand_to_basis(c))
    print('certificate tree:', cert.flow)
    print('sample:', H.sample_demand(0.05, rng=Random(20260930)))
