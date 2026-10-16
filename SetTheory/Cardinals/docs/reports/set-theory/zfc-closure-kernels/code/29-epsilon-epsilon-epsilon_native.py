"""Native epsilon / ground closure finite propositional-refutation certificates.

Research reference, not a compiled binary Turing machine or a formal proof.
Only generated ground-closure axioms and ground epsilon-critical formulas can enter
the public checker.  An accepting candidate is a finite Boolean refutation.
Host resource exhaustion is an exception, never an accepted refutation.

The interned DAG is syntax sharing only. No rewriting or epsilon evaluation
is used by the proof checker. See epsilon_final.tex for its ideal contract.
"""

from __future__ import annotations

from functools import lru_cache
from itertools import product
from math import isqrt
from typing import Iterable


class Invalid(ValueError):
    pass


class ResourceLimit(RuntimeError):
    pass


class Arena:
    """Two syntactic sorts; epsilon is the only binder and binds index zero.

    Below an epsilon binder, old free indices increase by one. At the root,
    free indices serve as stable labels, so forall_at removes a label without
    renumbering the remaining root labels. All final axioms are closed.
    """

    def __init__(self):
        self.nodes: list[tuple] = []
        self.index: dict[tuple, int] = {}
        self.bot = self._add(("b",))

    def _add(self, node: tuple) -> int:
        if node not in self.index:
            self.index[node] = len(self.nodes)
            self.nodes.append(node)
        return self.index[node]

    def sort(self, node: int) -> str:
        if type(node) is not int or not 0 <= node < len(self.nodes):
            raise Invalid("bad node reference")
        return "t" if self.nodes[node][0] in ("v", "e") else "f"

    def var(self, i: int) -> int:
        if type(i) is not int or i < 0:
            raise Invalid("bad variable index")
        return self._add(("v", i))

    def eps(self, body: int) -> int:
        if self.sort(body) != "f":
            raise Invalid("epsilon requires a formula")
        return self._add(("e", body))

    def rel(self, left: int, right: int) -> int:
        if self.sort(left) != "t" or self.sort(right) != "t":
            raise Invalid("relation requires terms")
        return self._add(("r", left, right))

    def imp(self, left: int, right: int) -> int:
        if self.sort(left) != "f" or self.sort(right) != "f":
            raise Invalid("implication requires formulas")
        return self._add(("i", left, right))

    def neg(self, a: int) -> int:
        return self.imp(a, self.bot)

    def conj(self, a: int, b: int) -> int:
        return self.neg(self.imp(a, self.neg(b)))

    def disj(self, a: int, b: int) -> int:
        return self.imp(self.neg(a), b)

    @lru_cache(maxsize=None)
    def free(self, node: int) -> frozenset[int]:
        n = self.nodes[node]
        if n[0] == "v":
            return frozenset((n[1],))
        if n[0] == "b":
            return frozenset()
        if n[0] == "e":
            return frozenset(i - 1 for i in self.free(n[1]) if i > 0)
        return self.free(n[1]) | self.free(n[2])

    def rebuild(self, node: tuple, children: tuple[int, ...]) -> int:
        if node[0] == "e":
            return self.eps(children[0])
        if node[0] == "r":
            return self.rel(*children)
        if node[0] == "i":
            return self.imp(*children)
        raise Invalid("only compound expressions can be rebuilt")

    @lru_cache(maxsize=None)
    def shift(self, root: int, amount: int, depth: int = 0) -> int:
        """Raise free indices; indices bound by inner epsilons are fixed."""
        n = self.nodes[root]
        if n[0] == "v":
            return self.var(n[1] + amount if n[1] >= depth else n[1])
        if n[0] == "b":
            return root
        deeper = depth + (n[0] == "e")
        return self.rebuild(n, tuple(self.shift(c, amount, deeper) for c in n[1:]))

    @lru_cache(maxsize=None)
    def substitute(self, root: int, label: int, term: int, depth: int = 0) -> int:
        """Replace one free root label; other root labels are retained."""
        if self.sort(term) != "t":
            raise Invalid("substitution payload is not a term")
        n = self.nodes[root]
        if n[0] == "v":
            return self.shift(term, depth) if n[1] == label + depth else root
        if n[0] == "b":
            return root
        deeper = depth + (n[0] == "e")
        return self.rebuild(n, tuple(self.substitute(c, label, term, deeper) for c in n[1:]))

    @lru_cache(maxsize=None)
    def abstract(self, root: int, label: int, depth: int = 0) -> int:
        """Add an outer binder for label, retaining other free labels."""
        n = self.nodes[root]
        if n[0] == "v":
            if n[1] < depth:
                return root
            return self.var(depth if n[1] == label + depth else n[1] + 1)
        if n[0] == "b":
            return root
        deeper = depth + (n[0] == "e")
        return self.rebuild(n, tuple(self.abstract(c, label, deeper) for c in n[1:]))

    def exists_at(self, label: int, body: int) -> int:
        witness = self.eps(self.abstract(body, label))
        return self.substitute(body, label, witness)

    def forall_at(self, label: int, body: int) -> int:
        counterexample = self.eps(self.abstract(self.neg(body), label))
        return self.substitute(body, label, counterexample)

    def critical(self, body: int, term: int) -> int:
        if self.sort(body) != "f" or not self.free(body) <= {0}:
            raise Invalid("critical matrix has a free parameter")
        if self.sort(term) != "t" or self.free(term):
            raise Invalid("critical instance requires a closed term")
        return self.imp(self.substitute(body, 0, term),
                        self.substitute(body, 0, self.eps(body)))

    def empty(self, x: int, z: int = 6) -> int:
        return self.forall_at(z, self.neg(self.rel(self.var(z), self.var(x))))

    def subset(self, y: int, b: int, z: int = 6) -> int:
        return self.forall_at(z, self.imp(self.rel(self.var(z), self.var(y)),
                                        self.rel(self.var(z), self.var(b))))

    def epsc2(self, matrix: int) -> int:
        """Full four-slot reference comparator, retaining outer forall p,q."""
        return self._native_wrapper(matrix, parameters=2)

    def ground_closure(self, matrix: int) -> int:
        """Primary two-slot generator: native rho(x,y), no outer parameters.

        Ground epsilon terms may occur anywhere in rho. Every object of the
        ground-term model is named, so all parameter assignments are covered
        by syntactically grounding them inside rho. This is not a claim that
        ordinary parameter-free EPSC has the same consistency strength.
        """
        return self._native_wrapper(matrix, parameters=0)

    def _native_wrapper(self, matrix: int, parameters: int) -> int:
        if self.sort(matrix) != "f" or not self.free(matrix) <= set(range(2 + parameters)):
            raise Invalid("native closure matrix has an unsupported free label")
        x, y, c, b, z = 0, 1, 2 + parameters, 3 + parameters, 4 + parameters
        vx, vy, vc = self.var(x), self.var(y), self.var(c)
        bound = self.forall_at(x, self.exists_at(b, self.forall_at(y,
                  self.imp(matrix, self.subset(y, b, z)))))
        active = self.disj(self.empty(x, z), self.rel(vx, vc))
        closure = self.forall_at(x, self.forall_at(y,
                    self.imp(self.conj(active, matrix), self.rel(vy, vc))))
        support = self.forall_at(y, self.imp(self.rel(vy, vc),
                                            self.exists_at(x, matrix)))
        hull = self.exists_at(c, self.conj(closure, support))
        result = self.imp(bound, hull)
        for parameter in reversed(range(2, 2 + parameters)):
            result = self.forall_at(parameter, result)
        if self.free(result):
            raise AssertionError("generated EPSC2 axiom is not closed")
        return result

    def propositional_atoms(self, formulas: Iterable[int]) -> list[int]:
        seen: set[int] = set()
        atoms: set[int] = set()
        stack = list(formulas)
        while stack:
            a = stack.pop()
            if a in seen:
                continue
            seen.add(a)
            node = self.nodes[a]
            if node[0] == "r":
                atoms.add(a)  # An atom's term bodies are not Boolean subformulas.
            elif node[0] == "i":
                stack.extend(node[1:])
            elif node[0] != "b":
                raise Invalid("propositional root is not a formula")
        return sorted(atoms)

    def unsat(self, formulas: Iterable[int], max_atoms: int | None = None) -> bool:
        """Exact exhaustive Boolean decision; no logical axioms are trusted."""
        formulas = tuple(formulas)
        if any(self.sort(a) != "f" or self.free(a) for a in formulas):
            raise Invalid("Boolean theory contains an open expression")
        atoms = self.propositional_atoms(formulas)
        if max_atoms is not None and len(atoms) > max_atoms:
            raise ResourceLimit(f"{len(atoms)} atoms exceed diagnostic limit {max_atoms}")
        for values in product((False, True), repeat=len(atoms)):
            valuation = dict(zip(atoms, values))

            @lru_cache(maxsize=None)
            def ev(a: int) -> bool:
                n = self.nodes[a]
                if n[0] == "b":
                    return False
                if n[0] == "r":
                    return valuation[a]
                return not ev(n[1]) or ev(n[2])

            if all(ev(a) for a in formulas):
                return False
        return True

    def verify(self, matrices: list[int], criticals: list[tuple[int, int]],
               max_atoms: int | None = None) -> bool:
        """Primary ground-theory accepting condition; no arbitrary assumptions."""
        formulas = [self.ground_closure(a) for a in matrices]
        formulas.extend(self.critical(a, t) for a, t in criticals)
        return self.unsat(formulas, max_atoms=max_atoms)

    def verify_full_reference(self, matrices: list[int], criticals: list[tuple[int, int]],
                              max_atoms: int | None = None) -> bool:
        """Independent four-slot comparator, not selected by certificate data."""
        formulas = [self.epsc2(a) for a in matrices]
        formulas.extend(self.critical(a, t) for a, t in criticals)
        return self.unsat(formulas, max_atoms=max_atoms)

    @lru_cache(maxsize=None)
    def natural_code(self, root: int) -> int:
        """Injective typed tree code, independent of DAG node numbers.

        Encoding a large expanded epsilon instance can exhaust host memory;
        the DAG checker does not need this optional reference representation.
        """
        n = self.nodes[root]
        if n[0] == "b":
            return 0
        if n[0] == "v":
            return 2 * n[1]
        if n[0] == "e":
            return 1 + 2 * self.natural_code(n[1])
        p = pair(self.natural_code(n[1]), self.natural_code(n[2]))
        return 1 + 2 * p if n[0] == "r" else 2 + 2 * p

    @lru_cache(maxsize=None)
    def natural_term(self, code: int) -> int:
        if type(code) is not int or code < 0:
            raise Invalid("term code must be natural")
        return self.var(code // 2) if code % 2 == 0 else self.eps(self.natural_formula(code // 2))

    @lru_cache(maxsize=None)
    def natural_formula(self, code: int) -> int:
        if type(code) is not int or code < 0:
            raise Invalid("formula code must be natural")
        if code == 0:
            return self.bot
        if code % 2:
            x, y = unpair(code // 2)
            return self.rel(self.natural_term(x), self.natural_term(y))
        x, y = unpair((code - 2) // 2)
        return self.imp(self.natural_formula(x), self.natural_formula(y))

    def raw_index_unsat(self, formulas: Iterable[int], max_index: int | None = None) -> bool:
        """State-oriented comparison: no distinct-atom table is required.

        Atom R(s,t) receives bit index pair(code(s),code(t)). Scan the finite
        formula forest for the maximum index, then try every full mask.
        Gaps in the indices are harmless; their valuation bits are ignored.
        This can be incomparably slower than unsat and is not a state count.
        """
        formulas = tuple(formulas)
        if any(self.sort(a) != "f" or self.free(a) for a in formulas):
            raise Invalid("Boolean theory contains an open expression")

        @lru_cache(maxsize=None)
        def atom_index(a: int) -> int:
            n = self.nodes[a]
            return pair(self.natural_code(n[1]), self.natural_code(n[2]))

        @lru_cache(maxsize=None)
        def bound(a: int) -> int:
            n = self.nodes[a]
            if n[0] == "b":
                return -1
            if n[0] == "r":
                return atom_index(a)
            return max(bound(n[1]), bound(n[2]))

        maximum = max((bound(a) for a in formulas), default=-1)
        if max_index is not None and maximum > max_index:
            raise ResourceLimit(f"atom index {maximum} exceeds diagnostic limit {max_index}")
        for mask in range(1 << (maximum + 1)):

            @lru_cache(maxsize=None)
            def ev(a: int) -> bool:
                n = self.nodes[a]
                if n[0] == "b":
                    return False
                if n[0] == "r":
                    return bool((mask >> atom_index(a)) & 1)
                return not ev(n[1]) or ev(n[2])

            if all(ev(a) for a in formulas):
                return False
        return True


class FiniteSemantics:
    """Independent diagnostic semantics; finite least witnesses, default 0.

    This is used by regressions, not by the accepting algorithm.
    Environments always have one slot for every external index in use.
    """

    def __init__(self, arena: Arena, size: int, relation: int):
        if size <= 0:
            raise Invalid("domains must be nonempty")
        self.a, self.size, self.relation = arena, size, relation

    def edge(self, x: int, y: int) -> bool:
        return bool((self.relation >> (x * self.size + y)) & 1)

    def value(self, root: int, env: tuple[int, ...]) -> int | bool:
        needed = self.a.free(root)
        if needed:
            if max(needed) >= len(env):
                raise Invalid("diagnostic environment is too short")
            env = tuple(env[i] if i in needed else 0 for i in range(max(needed) + 1))
        else:
            env = ()
        return self._value(root, env)

    @lru_cache(maxsize=None)
    def _value(self, root: int, env: tuple[int, ...]) -> int | bool:
        n = self.a.nodes[root]
        if n[0] == "v":
            return env[n[1]]
        if n[0] == "b":
            return False
        if n[0] == "e":
            return next((x for x in range(self.size)
                         if self.value(n[1], (x,) + env)), 0)
        if n[0] == "r":
            return self.edge(self.value(n[1], env), self.value(n[2], env))
        return not self.value(n[1], env) or self.value(n[2], env)

    def direct_epsc2(self, matrix: int) -> bool:
        """Quantifier-loop semantics of the original EPSC2 skeleton."""
        d = range(self.size)
        empty = [not any(self.edge(z, x) for z in d) for x in d]

        def sub(y: int, b: int) -> bool:
            return all(not self.edge(z, y) or self.edge(z, b) for z in d)

        for p in d:
            for q in d:
                rho = {(x, y): bool(self.value(matrix, (x, y, p, q)))
                       for x in d for y in d}
                bounded = all(any(all(not rho[x, y] or sub(y, b) for y in d)
                                  for b in d) for x in d)
                if not bounded:
                    continue
                found = False
                for c in d:
                    closure = all(not ((empty[x] or self.edge(x, c)) and rho[x, y])
                                  or self.edge(y, c) for x in d for y in d)
                    support = all(not self.edge(y, c) or any(rho[x, y] for x in d)
                                  for y in d)
                    if closure and support:
                        found = True
                        break
                if not found:
                    return False
        return True


TAGS = {"b": 0, "v": 1, "e": 2, "r": 3, "i": 4}


def pair(x: int, y: int) -> int:
    return (x + y) * (x + y + 1) // 2 + y


def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8 * n + 1) - 1) // 2
    y = n - s * (s + 1) // 2
    return s - y, y


def natural_list(code: int) -> list[int]:
    ans = []
    while code:
        head, code = unpair(code - 1)
        ans.append(head)
    return ans


def decode_natural_candidate(code: int) -> tuple[Arena, list[int], list[tuple[int, int]]]:
    """An alternative fair natural-number candidate space, with no bit parser."""
    if type(code) is not int or code < 0:
        raise Invalid("candidate code must be natural")
    a = Arena()
    matrix_codes, critical_codes = unpair(code)
    matrices = [a.natural_formula(m) for m in natural_list(matrix_codes)]
    criticals = []
    for pair_code in natural_list(critical_codes):
        m, t = unpair(pair_code)
        criticals.append((a.natural_formula(m), a.natural_term(t)))
    return a, matrices, criticals


def accepts_natural(code: int, max_atoms: int | None = None) -> bool:
    """The primary ground theory with the alternative natural candidate codec."""
    try:
        a, matrices, criticals = decode_natural_candidate(code)
        return a.verify(matrices, criticals, max_atoms=max_atoms)
    except Invalid:
        return False


def gamma(n: int) -> str:
    if type(n) is not int or n < 0:
        raise Invalid("natural number required")
    binary = bin(n + 1)[2:]
    return "0" * (len(binary) - 1) + binary


def encode_candidate(a: Arena, matrices: list[int], criticals: list[tuple[int, int]]) -> str:
    """A finite bit string, no padding: topological syntax DAG plus two lists."""
    used: set[int] = set()

    def visit(x: int):
        if x in used:
            return
        n = a.nodes[x]
        if n[0] not in ("b", "v"):
            for c in n[1:]:
                visit(c)
        used.add(x)

    for x in matrices:
        visit(x)
    for x, t in criticals:
        visit(x)
        visit(t)
    order = sorted(used)
    rename = {old: new for new, old in enumerate(order)}
    out = [gamma(len(order))]
    for old in order:
        n = a.nodes[old]
        out.append(f"{TAGS[n[0]]:03b}")
        if n[0] == "v":
            out.append(gamma(n[1]))
        elif n[0] != "b":
            out.extend(gamma(rename[c]) for c in n[1:])
    out.append(gamma(len(matrices)))
    out.extend(gamma(rename[x]) for x in matrices)
    out.append(gamma(len(criticals)))
    for x, t in criticals:
        out.extend((gamma(rename[x]), gamma(rename[t])))
    return "".join(out)


def decode_candidate(bits: str) -> tuple[Arena, list[int], list[tuple[int, int]]]:
    if not isinstance(bits, str) or any(c not in "01" for c in bits):
        raise Invalid("candidate must be a bit string")
    at = 0

    def read(k: int) -> str:
        nonlocal at
        if at + k > len(bits):
            raise Invalid("truncated candidate")
        ans, at = bits[at:at + k], at + k
        return ans

    def natural() -> int:
        zeros = 0
        while read(1) == "0":
            zeros += 1
        return int("1" + read(zeros), 2) - 1

    a, refs = Arena(), []
    count = natural()
    for _ in range(count):
        tag = int(read(3), 2)

        def ref() -> int:
            j = natural()
            if j >= len(refs):
                raise Invalid("forward, cyclic, or absent node reference")
            return refs[j]

        if tag == 0:
            node = a.bot
        elif tag == 1:
            node = a.var(natural())
        elif tag == 2:
            node = a.eps(ref())
        elif tag == 3:
            node = a.rel(ref(), ref())
        elif tag == 4:
            node = a.imp(ref(), ref())
        else:
            raise Invalid("unknown node constructor")
        refs.append(node)

    def final_ref() -> int:
        i = natural()
        if i >= len(refs):
            raise Invalid("absent root reference")
        return refs[i]

    matrices = [final_ref() for _ in range(natural())]
    criticals = [(final_ref(), final_ref()) for _ in range(natural())]
    if at != len(bits):
        raise Invalid("trailing candidate data")
    return a, matrices, criticals


def accepts_bits(bits: str, max_atoms: int | None = None) -> bool:
    """Invalid syntax is rejected. Host resource exceptions propagate."""
    try:
        a, matrices, criticals = decode_candidate(bits)
        return a.verify(matrices, criticals, max_atoms=max_atoms)
    except Invalid:
        return False


def candidate_strings():
    """Every finite bit string exactly once, in increasing length order."""
    yield ""
    width = 1
    while True:
        for n in range(1 << width):
            yield f"{n:0{width}b}"
        width += 1


def ideal_search():
    """Mathematical unbounded search. Do not mistake finite prefixes for evidence."""
    for bits in candidate_strings():
        if accepts_bits(bits):
            return bits

