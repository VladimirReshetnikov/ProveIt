"""Exact SU(2) formula compilers for validated knots and word presentations.

The theoretical bounds use singly exponential real-algebraic decision.
The optional Z3/NLSAT adapter is exact when it returns sat or unsat, but is
not asserted to realize that complexity bound. Limits return INCONCLUSIVE.
No general presentation is assigned a knot verdict without diagram provenance.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from math import isfinite
from time import monotonic


class SU2Limit(RuntimeError):
    """A compiler resource limit; it is never a mathematical verdict."""


class Ring:
    """Small exact sparse integer polynomial ring, with explicit term caps."""

    def __init__(self, *, max_terms=200_000, max_work=5_000_000,
                 check=lambda: None):
        for name, value in (("max_terms", max_terms), ("max_work", max_work)):
            if value is not None and (type(value) is not int or value < 0):
                raise ValueError(f"{name} must be a nonnegative integer or None")
        self.names, self.work = [], 0
        self.max_terms, self.max_work, self.check = max_terms, max_work, check

    def tick(self, amount=1):
        self.check()
        self.work += amount
        if self.max_work is not None and self.work > self.max_work:
            raise SU2Limit("SU2 polynomial work allowance exhausted")

    def size(self, p):
        if self.max_terms is not None and len(p) > self.max_terms:
            raise SU2Limit("SU2 polynomial term allowance exhausted")
        return p

    def var(self, name):
        self.tick()
        result = {(len(self.names),): 1}
        self.names.append(name)
        return result

    @staticmethod
    def const(value):
        return {(): value} if value else {}

    def add(self, *polynomials):
        result = {}
        for p in polynomials:
            for m, coefficient in p.items():
                self.tick()
                value = result.get(m, 0) + coefficient
                if value:
                    result[m] = value
                else:
                    result.pop(m, None)
            self.size(result)
        return result

    def neg(self, p):
        self.tick(len(p))
        return {m: -c for m, c in p.items()}

    def sub(self, p, q):
        return self.add(p, self.neg(q))

    def mul(self, p, q):
        if not p or not q:
            return {}
        result = {}
        for a, ca in p.items():
            for b, cb in q.items():
                self.tick()
                m = tuple(sorted(a + b))
                value = result.get(m, 0) + ca * cb
                if value:
                    result[m] = value
                else:
                    result.pop(m, None)
            self.size(result)
        return result

    def squares(self, polynomials):
        result = {}
        for p in polynomials:
            result = self.add(result, self.mul(p, p))
        return result


def quaternion_mul(ring, p, q):
    a, b, c, d = p
    e, f, g, h = q
    mul, add, neg = ring.mul, ring.add, ring.neg
    return (add(mul(a, e), neg(mul(b, f)), neg(mul(c, g)), neg(mul(d, h))),
            add(mul(a, f), mul(b, e), mul(c, h), neg(mul(d, g))),
            add(mul(a, g), neg(mul(b, h)), mul(c, e), mul(d, f)),
            add(mul(a, h), mul(b, g), neg(mul(c, f)), mul(d, e)))


def quaternion_inverse(ring, q):
    return (q[0], *(ring.neg(p) for p in q[1:]))


def _identity(ring):
    return (ring.const(1), {}, {}, {})


def _new_quaternion(ring, prefix):
    return tuple(ring.var(f"{prefix}_{c}") for c in "abcd")


def _generator_quaternions(ring, generators, *, meridional=False, gauge=True):
    # Simultaneous SU(2) conjugation is an SO(3) rotation on imaginary parts.
    # Rotate the first vector to the x-axis and the second into the xy-plane.
    # Zero or parallel vectors cause no exception to the existence argument.
    result, trace = {}, None
    for i, g in enumerate(generators):
        scalar = trace if meridional and trace is not None else ring.var(f"g{g}_a")
        if trace is None:
            trace = scalar
        vector = tuple({} if gauge and (i == 0 and j >= 1 or i == 1 and j == 2)
                       else ring.var(f"g{g}_{'bcd'[j]}") for j in range(3))
        result[g] = (scalar, *vector)
    return result


def _equal_quaternions(ring, left, right):
    return [ring.sub(a, b) for a, b in zip(left, right)]


def _norm(ring, q):
    return ring.sub(ring.squares(q), ring.const(1))


def _nonabelian(ring, generators, *, meridional=False):
    """Distinct images suffice ONLY for a certified conjugate generating set."""
    values = list(generators.values())
    if meridional:
        return ring.squares(ring.sub(a, b) for q in values[1:]
                            for a, b in zip(q, values[0])) if values else {}
    differences = []
    for i, q in enumerate(values):
        for p in values[i + 1:]:
            differences.extend(_equal_quaternions(
                ring, quaternion_mul(ring, q, p), quaternion_mul(ring, p, q)))
    return ring.squares(differences)


def _degree(p):
    return max(map(len, p), default=0)


def _poly_smt(p, names):
    def integer(c):
        return str(c) if c >= 0 else f"(- {-c})"
    terms = []
    for monomial, coefficient in sorted(p.items()):
        factors = [names[v] for v in monomial]
        if coefficient != 1 or not factors:
            factors.insert(0, integer(coefficient))
        terms.append(factors[0] if len(factors) == 1 else "(* " + " ".join(factors) + ")")
    return "0" if not terms else terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"


@dataclass
class Formula:
    ring: Ring
    equations: list
    nonabelian: dict
    metadata: dict

    def summary(self):
        polys = self.equations + [self.nonabelian]
        maximum = max((_degree(p) for p in self.equations), default=0)
        return dict(self.metadata, real_variables=len(self.ring.names),
                    equations=len(self.equations), max_equation_degree=maximum,
                    aggregate_degree_bound=max(2 * maximum, _degree(self.nonabelian)),
                    polynomial_terms=sum(map(len, polys)),
                    largest_polynomial_terms=max(map(len, polys), default=0),
                    coefficient_bits=max((abs(c).bit_length() for p in polys
                                          for c in p.values()), default=0),
                    compiler_work=self.ring.work)

    def to_smt2(self, *, aggregate=False, timeout_ms=None):
        equations = ([self.ring.squares(self.equations)] if aggregate else self.equations)
        lines = ["; Exact polynomial reals. sat = nonabelian representation.",
                 "(set-logic QF_NRA)"]
        if timeout_ms is not None:
            if type(timeout_ms) is not int or timeout_ms < 0:
                raise ValueError("timeout_ms must be a nonnegative integer or None")
            lines.append(f"(set-option :timeout {timeout_ms})")
        lines += [f"(declare-fun {name} () Real)" for name in self.ring.names]
        lines += [f"(assert (= {_poly_smt(p, self.ring.names)} 0))" for p in equations]
        lines.append(f"(assert (> {_poly_smt(self.nonabelian, self.ring.names)} 0))")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"

    def evaluate(self, assignment):
        """Exact with Fraction/algebraic inputs; useful for independent witnesses."""
        values = [assignment[name] for name in self.ring.names]
        def value(p):
            total = 0
            for monomial, coefficient in p.items():
                term = coefficient
                for variable in monomial:
                    term *= values[variable]
                total += term
            return total
        return [value(p) for p in self.equations], value(self.nonabelian)


def _validate_generators(generators):
    generators = tuple(generators)
    if (not generators or any(type(g) is not int or g <= 0 for g in generators)
            or len(set(generators)) != len(generators)):
        raise ValueError("generators must be distinct positive integers")
    return tuple(sorted(generators))


def _chunk_word(ring, word, generators, equations, chunk_size, auxiliary):
    current = _identity(ring)
    for i, letter in enumerate(word, 1):
        if type(letter) is not int or abs(letter) not in generators:
            raise ValueError("relator contains an unknown generator")
        q = generators[abs(letter)]
        if letter < 0:
            q = quaternion_inverse(ring, q)
        current = quaternion_mul(ring, current, q)
        if i < len(word) and i % chunk_size == 0:
            name = _new_quaternion(ring, f"u{auxiliary[0]}")
            auxiliary[0] += 1
            equations.extend(_equal_quaternions(ring, name, current))
            current = name
    return current


def _compile_words(generators, relators, *, chunk_size=None, gauge=True,
                   meridional=False, **limits):
    generators = _validate_generators(generators)
    relators = [tuple(w) for w in relators]
    total = sum(map(len, relators))
    chunk_size = max(1, (total + len(generators) - 1) // len(generators)) if chunk_size is None else chunk_size
    if type(chunk_size) is not int or chunk_size < 1:
        raise ValueError("chunk_size must be a positive integer or None")
    ring = Ring(**limits)
    quaternions = _generator_quaternions(ring, generators, gauge=gauge, meridional=meridional)
    equations = [_norm(ring, q) for q in quaternions.values()]
    auxiliary = [0]
    for word in relators:
        q = _chunk_word(ring, word, quaternions, equations, chunk_size, auxiliary)
        equations.extend(_equal_quaternions(ring, q, _identity(ring)))
    nonabelian = _nonabelian(ring, quaternions, meridional=meridional)
    return Formula(ring, equations, nonabelian,
                   dict(encoding="presentation-chunks", generators=len(generators),
                        relators=len(relators), expanded_letters=total,
                        chunk_size=chunk_size, auxiliary_quaternions=auxiliary[0],
                        gauge=bool(gauge), knot_provenance=False))


def compile_presentation(generators, relators, *, chunk_size=None, gauge=True,
                         max_terms=200_000, max_work=5_000_000, check=lambda: None):
    """General finite presentation; always use the commutator inequality.

    Only the validated diagram constructors may certify conjugate meridians.
    This interface returns a representation query, not a knot verdict.
    """
    return _compile_words(generators, relators, chunk_size=chunk_size, gauge=gauge,
                          meridional=False, max_terms=max_terms,
                          max_work=max_work, check=check)


def wirtinger_presentation(diagram):
    """Recover a presentation by oriented traversal, independently of DSU naming."""
    from .diagram import Diagram
    diagram = Diagram.from_pd(diagram.pd)
    n = diagram.crossings
    if not n:
        return (1,), []
    current, under, over = 1, {}, {}
    for dart in diagram.traversal():
        crossing = dart // 4
        if dart % 2:
            over[crossing] = current
        else:
            nxt = current % n + 1
            under[crossing] = (current, nxt)
            current = nxt
    words = []
    for crossing, sign in enumerate(diagram.signs()):
        source, target = under[crossing]
        conjugator = sign * over[crossing]
        words.append((conjugator, source, -conjugator, -target))
    return tuple(range(1, n + 1)), words


def _free_reduce(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    left, right = 0, len(stack)
    while right - left > 1 and stack[left] == -stack[right - 1]:
        left, right = left + 1, right - 1
    return tuple(stack[left:right])


def simplify_presentation(generators, relators, *, max_letters=100_000,
                           max_moves=100_000, check=lambda: None):
    """Bounded defining-generator Tietze elimination, preserving every relation.

    Returns the exact stalled presentation and a replayable move list, even
    when it cannot prove cyclicity. There is no polynomial expansion claim.
    """
    generators = set(_validate_generators(generators))
    if any(type(x) is not int or x < 0 for x in (max_letters, max_moves)):
        raise ValueError("presentation allowances must be nonnegative integers")
    raw = [tuple(w) for w in relators]
    if any(type(x) is not int or abs(x) not in generators for w in raw for x in w):
        raise ValueError("invalid presentation letter")
    words = [_free_reduce(w) for w in raw]
    if sum(map(len, words)) > max_letters:
        raise SU2Limit("initial presentation exceeds expanded-letter allowance")
    moves = []
    while len(generators) > 1 and len(moves) < max_moves:
        check()
        counts = Counter(abs(x) for w in words for x in w)
        total = sum(map(len, words))
        choices = []
        for i, w in enumerate(words):
            check()
            for g, count in Counter(map(abs, w)).items():
                if count == 1:
                    predicted = total - len(w) + (counts[g] - 1) * (len(w) - 2)
                    choices.append((predicted, len(w), i, g))
        if not choices:
            break
        predicted, _, index, g = min(choices)
        if predicted > max_letters:
            break
        word = words[index]
        position = next(i for i, x in enumerate(word) if abs(x) == g)
        remainder = word[position + 1:] + word[:position]
        image = tuple(-x for x in reversed(remainder)) if word[position] > 0 else remainder
        inverse = tuple(-x for x in reversed(image))
        words[index] = ()
        updated = []
        for w in words:
            check()
            updated.append(_free_reduce(y for x in w for y in
                                        (image if x == g else inverse if x == -g else (x,))))
        words = updated
        generators.remove(g)
        moves.append(dict(relation=index, generator=g))
    return dict(generators=tuple(sorted(generators)), relators=words, moves=moves,
                expanded_letters=sum(map(len, words)))


def compile_diagram_presentation(diagram, *, simplify=True, chunk_size=None,
                                 max_letters=100_000, **limits):
    generators, relators = wirtinger_presentation(diagram)
    trace = dict(generators=generators, relators=relators, moves=[])
    if simplify:
        trace = simplify_presentation(generators, relators, max_letters=max_letters,
                                      check=limits.get('check', lambda: None))
    # Defining-generator elimination retains a subset of the original
    # positively oriented meridians; their common conjugacy class is preserved.
    formula = _compile_words(trace['generators'], trace['relators'], meridional=True,
                              chunk_size=chunk_size, **limits)
    formula.metadata.update(encoding='tietze-chunks' if simplify else 'wirtinger-words',
                            input_crossings=diagram.crossings, knot_provenance=True,
                            common_meridional_trace=True,
                            defining_eliminations=len(trace['moves']))
    return formula, trace


def bridge_presentation(diagram):
    """Eliminate under-only Wirtinger arcs along each actual underpass.

    b is the number of over-runs in THIS diagram, not the bridge invariant.
    Each record (source, target, w) means target*w = w*source.
    """
    from .diagram import Diagram
    diagram = Diagram.from_pd(diagram.pd)  # Validate even manually constructed Diagram objects.
    walk = diagram.traversal()
    if not walk:
        return dict(generators=(1,), conjugacies=[], crossings=0, overpasses=0)
    start = next(i for i, d in enumerate(walk) if d % 2 and not walk[i - 1] % 2)
    walk = walk[start:] + walk[:start]
    over, current, previous = {}, 0, False
    for dart in walk:
        if dart % 2:
            if not previous:
                current += 1
            over[dart // 4] = current
        previous = bool(dart % 2)
    b = current
    signs = diagram.signs()
    records, under = [], []
    current = 0
    previous = False
    for dart in walk:
        if dart % 2:
            if not previous:
                if current:
                    records.append((current, current + 1, tuple(reversed(under))))
                current += 1
                under = []
        else:
            under.append(signs[dart // 4] * over[dart // 4])
        previous = bool(dart % 2)
    records.append((b, 1, tuple(reversed(under))))
    if sum(len(w) for _, _, w in records) != diagram.crossings:
        raise ArithmeticError("bridge extraction did not cover all undercrossings")
    return dict(generators=tuple(range(1, b + 1)), conjugacies=records,
                crossings=diagram.crossings, overpasses=b)


def compile_bridge(diagram, *, chunk_size=None, gauge=True, **limits):
    presentation = bridge_presentation(diagram)
    r = len(presentation['generators'])
    n = presentation['crossings']
    chunk_size = max(1, (n + r - 1) // r) if chunk_size is None else chunk_size
    if type(chunk_size) is not int or chunk_size < 1:
        raise ValueError("chunk_size must be a positive integer or None")
    ring = Ring(**limits)
    quaternions = _generator_quaternions(ring, presentation['generators'],
                                        meridional=True, gauge=gauge)
    equations = [_norm(ring, q) for q in quaternions.values()]
    auxiliary = [0]
    for source, target, word in presentation['conjugacies']:
        w = _chunk_word(ring, word, quaternions, equations, chunk_size, auxiliary)
        equations.extend(_equal_quaternions(
            ring, quaternion_mul(ring, quaternions[target], w),
            quaternion_mul(ring, w, quaternions[source])))
    nonabelian = _nonabelian(ring, quaternions, meridional=True)
    return Formula(ring, equations, nonabelian,
                   dict(encoding="bridge-chunks", generators=r,
                        crossings=n, overpasses=presentation['overpasses'],
                        conjugator_letters=n, chunk_size=chunk_size,
                        auxiliary_quaternions=auxiliary[0], gauge=bool(gauge),
                        common_meridional_trace=True, knot_provenance=True))


def compile_slp(generators, arena, roots, *, inline_degree=1, gauge=True, **limits):
    """Compile WordArena relators, retaining sharing and cutting large products.

    inline_degree=1 gives one quaternion per reachable product gate and
    equations of degree <=2. Larger thresholds trade variables for degree.
    Only the integer generator/concatenation grammar is accepted.
    """
    generators = _validate_generators(generators)
    if type(inline_degree) is not int or inline_degree < 1:
        raise ValueError("inline_degree must be a positive integer")
    roots = tuple(roots)
    pending, reachable = list(roots), set()
    while pending:
        node = pending.pop()
        if type(node) is not int or not 0 <= node < len(arena.rules):
            raise ValueError("invalid SLP node")
        if node == 0 or node in reachable:
            continue
        reachable.add(node)
        rule = arena.rules[node]
        if len(rule) == 2 and rule[0] == 't':
            if type(rule[1]) is not int or abs(rule[1]) not in generators:
                raise ValueError("invalid SLP letter")
        elif len(rule) == 3 and rule[0] == 'c':
            if any(type(x) is not int or not 0 <= x < node for x in rule[1:]):
                raise ValueError("SLP must be acyclic and topologically numbered")
            pending.extend(rule[1:])
        else:
            raise ValueError("invalid SLP production")
    ring = Ring(**limits)
    quaternions = _generator_quaternions(ring, generators, gauge=gauge)
    equations = [_norm(ring, q) for q in quaternions.values()]
    expressions, degrees = {0: _identity(ring)}, {0: 0}
    cuts, products = 0, 0
    for node in sorted(reachable):
        rule = arena.rules[node]
        if rule[0] == 't':
            q = quaternions[abs(rule[1])]
            expressions[node] = quaternion_inverse(ring, q) if rule[1] < 0 else q
            degrees[node] = 1
        else:
            products += 1
            _, left, right = rule
            q = quaternion_mul(ring, expressions[left], expressions[right])
            degree = degrees[left] + degrees[right]
            if degree > inline_degree:
                name = _new_quaternion(ring, f"u{cuts}")
                cuts += 1
                equations.extend(_equal_quaternions(ring, name, q))
                q, degree = name, 1
            expressions[node], degrees[node] = q, degree
    for root in roots:
        equations.extend(_equal_quaternions(ring, expressions[root], _identity(ring)))
    return Formula(ring, equations, _nonabelian(ring, quaternions),
                   dict(encoding="slp-cuts", generators=len(generators),
                        relators=len(roots), reachable_nodes=len(reachable),
                        product_gates=products, auxiliary_quaternions=cuts,
                        inline_degree=inline_degree, gauge=bool(gauge), knot_provenance=False))


def solve_formula(formula, *, seconds=1.0, aggregate=False, trace_zero_probe=False):
    """Optional exact NLSAT; no floating-point or delta-sat acceptance."""
    if seconds is not None and (type(seconds) not in (int, float)
                                or not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative, or None")
    if seconds == 0:
        return dict(status="INCONCLUSIVE", reason="zero SU2 solver allowance")
    try:
        import z3
    except ImportError:
        return dict(status="INCONCLUSIVE", reason="optional z3-solver is unavailable")
    start = monotonic()
    solver = z3.SolverFor("QF_NRA")
    solver.from_string(formula.to_smt2(aggregate=aggregate))
    expires = None if seconds is None else start + seconds
    probe = False
    answer = None
    if trace_zero_probe:
        scalar = next((name for name in formula.ring.names
                       if name.startswith('g') and name.endswith('_a')), None)
        if scalar is not None:
            probe_solver = z3.SolverFor('QF_NRA')
            probe_solver.add(*solver.assertions(), z3.Real(scalar) == 0)
            allowance = 0.15 if seconds is None else min(0.15, seconds / 3)
            probe_solver.set(timeout=max(1, int(1000 * allowance)))
            probe_answer = probe_solver.check()
            if probe_answer == z3.sat:
                solver, answer, probe = probe_solver, probe_answer, True
            # unsat or unknown for this restricted query says nothing about
            # the original formula, so the complete query still runs.
    if answer is None:
        remaining = None if expires is None else expires - monotonic()
        if remaining is not None and remaining <= 0:
            return dict(status='INCONCLUSIVE', reason='SU2 solver allowance exhausted')
        if remaining is not None:
            solver.set(timeout=max(1, int(1000 * remaining)))
        answer = solver.check()
    status = "NONABELIAN" if answer == z3.sat else "NO_NONABELIAN" if answer == z3.unsat else "INCONCLUSIVE"
    result = dict(status=status, solver="Z3 NLSAT",
                  solver_version=z3.get_version_string(), trace_zero_witness=probe,
                  seconds=monotonic() - start)
    if answer == z3.unknown:
        result['reason'] = solver.reason_unknown()
    elif answer == z3.sat:
        model = solver.model()
        # Preserve exact SMT-LIB algebraic expressions, never rounded decimals.
        result['model'] = {name: model.eval(z3.Real(name), model_completion=True).sexpr()
                           for name in formula.ring.names}
        result['model_checked_exactly'] = all(z3.is_true(model.eval(p, model_completion=True))
                                              for p in solver.assertions())
        if not result['model_checked_exactly']:
            raise ArithmeticError('SU2 solver model failed exact substitution')
    return result


def su2_decide(diagram, *, seconds=1.0, chunk_size=None, max_terms=200_000,
               max_work=5_000_000, presentation='bridge', trace_zero_probe=False,
               check=lambda: None):
    """Validated PD -> bridge formula -> exact solver, sharing a local deadline."""
    if seconds is not None and (type(seconds) not in (int, float)
                                or not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative, or None")
    start = monotonic()
    expires = None if seconds is None else start + seconds
    def tick():
        check()
        if expires is not None and monotonic() >= expires:
            raise SU2Limit("SU2 local time allowance exhausted")
    try:
        tick()
        options = dict(chunk_size=chunk_size, max_terms=max_terms, max_work=max_work, check=tick)
        if presentation == 'bridge':
            formula = compile_bridge(diagram, **options)
        elif presentation in ('tietze', 'wirtinger'):
            formula, _ = compile_diagram_presentation(
                diagram, simplify=presentation == 'tietze', **options)
        else:
            raise ValueError("presentation must be bridge, tietze, or wirtinger")
        tick()
        remaining = None if expires is None else max(0, expires - monotonic())
        result = solve_formula(formula, seconds=remaining, trace_zero_probe=trace_zero_probe)
        # A global cancellation propagates even when a local query finishes.
        check()
        result['status'] = {'NONABELIAN': 'KNOTTED', 'NO_NONABELIAN': 'UNKNOT'}.get(
            result['status'], 'INCONCLUSIVE')
        result.update(formula=formula.summary(), seconds=monotonic() - start)
        return result
    except SU2Limit as exc:
        check()
        return dict(status='INCONCLUSIVE', reason=str(exc), seconds=monotonic() - start)


def main():
    import argparse
    import json
    from pathlib import Path
    from .diagram import Diagram
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--seconds', type=float, default=1.0)
    parser.add_argument('--chunk-size', type=int)
    parser.add_argument('--presentation', choices=['bridge', 'tietze', 'wirtinger'], default='bridge')
    parser.add_argument('--trace-zero-probe', action='store_true',
                        help='try a restricted SAT witness before the complete query')
    parser.add_argument('--smt2', type=Path, help='write a replayable exact formula')
    parser.add_argument('--compile-only', action='store_true')
    args = parser.parse_args()
    diagram = Diagram.from_json(json.loads(args.input.read_text()))
    if args.smt2 or args.compile_only:
        formula = (compile_bridge(diagram, chunk_size=args.chunk_size) if args.presentation == 'bridge'
                   else compile_diagram_presentation(diagram, chunk_size=args.chunk_size,
                          simplify=args.presentation == 'tietze')[0])
        if args.smt2:
            args.smt2.write_text(formula.to_smt2())
        if args.compile_only:
            print(json.dumps(formula.summary(), indent=2))
            return
    print(json.dumps(su2_decide(diagram, seconds=args.seconds,
                               chunk_size=args.chunk_size, presentation=args.presentation,
                               trace_zero_probe=args.trace_zero_probe), indent=2))


if __name__ == '__main__':
    main()
