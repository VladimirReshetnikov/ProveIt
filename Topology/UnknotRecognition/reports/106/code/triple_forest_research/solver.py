"""Forest-compatible peeling with few exceptional three-row columns.

The deterministic solver is exact when uncapped.  The randomized solver has
one-sided failure: it returns a separately replayable SUCCESS, or INCONCLUSIVE.
Neither solver authenticates a manifold or decides a knot type.

The unchanged ``base`` and ``base_verify`` kernels are vendored from the
2026-10-12 incoming Dual Forest Normalization report; see ATTRIBUTION.md.
"""

from itertools import permutations, product
from random import Random, SystemRandom

from . import base


DEFAULT_PRIME = (1 << 61) - 1


def _bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def _prepare(data, work, *, support_bound=3):
    count = len(data[3])
    owners = {}
    for row, entries in enumerate(data[3]):
        for column, value in entries:
            work.tick("dependency_entries")
            owners.setdefault(column, []).append((row, value))
    triples, incoming, seeds = [], [[] for _ in range(count)], set()
    ordinary = set()
    for column, entries in sorted(owners.items()):
        unit = tuple(row for row, value in entries if value == 1)
        if not unit:
            continue
        if support_bound is not None and len(entries) > support_bound:
            return None
        if len(entries) > 2:
            triples.append((column, tuple(row for row, _ in entries), unit))
        else:
            ordinary.add(column)
            if len(entries) == 1:
                seeds.add(entries[0][0])
            else:
                for target in unit:
                    incoming[target].extend(row for row, _ in entries if row != target)
    # All transitive ancestor sets, including the vertex itself.  This simple
    # O(R(R+I)) implementation deliberately avoids a hidden search oracle.
    ancestors = []
    for row in range(count):
        reached, stack = 1 << row, [row]
        while stack:
            vertex = stack.pop()
            work.tick("ancestor_vertices")
            for previous in incoming[vertex]:
                work.tick("ancestor_arcs")
                if not reached & (1 << previous):
                    reached |= 1 << previous
                    stack.append(previous)
        ancestors.append(reached)
    reach = [0] * count
    for target, mask in enumerate(ancestors):
        for previous in _bits(mask):
            work.tick("reachability_pairs")
            reach[previous] |= 1 << target
    known = 0
    for row in seeds:
        known |= reach[row]
    ordinary_rows = tuple(tuple((c, a) for c, a in row if c in ordinary)
                          for row in data[3])
    groups = base._degree_two_groups((*data[:3], ordinary_rows), work)
    eligible = sum(1 << row for row, edge in enumerate(data[2])
                   if edge is not None and edge[0] != edge[1])
    return dict(triples=triples, ancestors=ancestors, reach=reach,
                known=known, source_groups=groups, eligible=eligible)


def _histories(prepared):
    triples = prepared["triples"]
    for length in range(len(triples) + 1):
        for order in permutations(range(len(triples)), length):
            for targets in product(*(triples[index][2] for index in order)):
                yield tuple(zip(order, targets))


def _obligations(prepared, history, work):
    known, target_mask, requirements = prepared["known"], 0, set()
    eligible = prepared["eligible"]
    for index, target in history:
        _, rows, _ = prepared["triples"][index]
        for row in rows:
            work.tick("prerequisite_tests")
            if row != target and not known & (1 << row):
                requirement = prepared["ancestors"][row] & eligible
                if not requirement:
                    return None
                requirements.add(requirement)
        known |= prepared["reach"][target]
        target_mask |= 1 << target
    mandatory = []
    for group in prepared["source_groups"]:
        mask = sum(1 << row for row in group)
        if mask & target_mask:
            continue
        mask &= eligible
        if not mask:
            return None
        mandatory.append(mask)
    # Any hit of a smaller required set also hits a superset.  A mandatory
    # group contained in a prerequisite makes that prerequisite automatic.
    reduced = []
    for mask in sorted(requirements, key=lambda x: (x.bit_count(), x)):
        if any(other & mask == other for other in (*mandatory, *reduced)):
            continue
        reduced.append(mask)
    work.tick("required_set_reductions", len(requirements))
    return tuple(sorted(mandatory)), tuple(sorted(reduced))


def _forced_cover(data, mandatory, requirements, work):
    """Enumerate only prerequisite representatives; intersect the rest."""
    visited = set()
    for representatives in product(*(_bits(mask) for mask in requirements)):
        work.tick("representative_tuples")
        forced = frozenset(representatives)
        if forced in visited:
            continue
        if len(visited) < 4096:
            visited.add(forced)
        if not base._graphic_independent(data, forced, work):
            continue
        dsu = base._forest(data, forced, work)
        contracted = tuple(None if edge is None else
                           (dsu.find(edge[0]), dsu.find(edge[1]))
                           for edge in data[2])
        contracted_data = (data[0], data[1], contracted, data[3])
        forced_mask = sum(1 << row for row in forced)
        groups = [list(_bits(mask)) for mask in mandatory if not mask & forced_mask]
        chosen, failure = base._rainbow_forest(contracted_data, groups, work)
        if failure is None:
            return base._extend_tree(data, forced | set(chosen), work)
    return None


def _prime64(number):
    """Deterministic Miller--Rabin for the explicitly bounded 64-bit domain."""
    if type(number) is not int or not 2 <= number < (1 << 64):
        return False
    for small in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if number % small == 0:
            return number == small
    odd, shifts = number - 1, 0
    while odd % 2 == 0:
        odd //= 2
        shifts += 1
    for witness in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if witness % number == 0:
            continue
        value = pow(witness, odd, number)
        if value in (1, number - 1):
            continue
        for _ in range(shifts - 1):
            value = value * value % number
            if value == number - 1:
                break
        else:
            return False
    return True


def _determinant(matrix, prime, work):
    size = len(matrix)
    answer = 1
    for column in range(size):
        pivot = next((row for row in range(column, size)
                      if matrix[row][column] % prime), None)
        work.tick("determinant_pivot_tests", size - column)
        if pivot is None:
            return 0
        if pivot != column:
            matrix[pivot], matrix[column] = matrix[column], matrix[pivot]
            answer = -answer
        value = matrix[column][column] % prime
        answer = answer * value % prime
        inverse = pow(value, prime - 2, prime)
        for row in range(column + 1, size):
            multiplier = matrix[row][column] * inverse % prime
            if multiplier:
                for other in range(column + 1, size):
                    matrix[row][other] = (matrix[row][other]
                                          - multiplier * matrix[column][other]) % prime
                work.tick("field_elimination_updates", size - column - 1)
    return answer % prime


class CoverageSieve:
    """Common-basis determinant with exact inclusion--exclusion on colors.

    The columns for a mandatory representative and for a filler use distinct
    random variables even when they come from the same original edge.
    """

    def __init__(self, data, mandatory, requirements, prime, rng, work,
                 coefficients=None, mask_coefficients=None):
        self.rank = data[0] - 1
        self.prime, self.work = prime, work
        self.colors = len(requirements)
        self.coefficients = coefficients
        self.mask_coefficients = mask_coefficients
        self.copies = []
        self.impossible = len(mandatory) > self.rank
        group_of = {row: group for group, mask in enumerate(mandatory)
                    for row in _bits(mask)}
        filler_rank = self.rank - len(mandatory)
        if filler_rank < 0:
            return
        eligible = [row for row, edge in enumerate(data[2])
                    if edge is not None and edge[0] != edge[1]]
        if prime <= 2 * len(eligible):
            raise base.InvalidProblem("prime must exceed twice the eligible edge count")
        for label, row in enumerate(eligible, 1):
            edge = data[2][row]
            vector_a = tuple((vertex - 1, sign) for vertex, sign in
                             ((edge[0], 1), (edge[1], -1)) if vertex != 0)
            color_mask = sum(1 << index for index, mask in enumerate(requirements)
                             if mask & (1 << row))
            if row in group_of:
                self.copies.append((row, vector_a, ((group_of[row], 1),),
                                    color_mask, rng.randrange(prime)))
            if filler_rank:
                powers, power = [], 1
                for index in range(filler_rank):
                    powers.append((len(mandatory) + index, power))
                    power = power * label % prime
                self.copies.append((row, vector_a, tuple(powers), color_mask,
                                    rng.randrange(prime)))
        work.tick("sieve_copies", len(self.copies))

    def evaluate(self, active):
        answer = 0
        entries = (self.mask_coefficients if self.mask_coefficients is not None else
                   ((missing, (-1 if missing.bit_count() % 2 else 1)
                     if self.coefficients is None else self.coefficients[missing])
                    for missing in range(1 << self.colors)))
        for missing, coefficient in entries:
            if coefficient % self.prime == 0:
                continue
            self.work.tick("sieve_determinants")
            matrix = [[0] * self.rank for _ in range(self.rank)]
            for index in sorted(active):
                _, vector_a, vector_b, colors, weight = self.copies[index]
                self.work.tick("sieve_copy_visits")
                if colors & missing:
                    continue
                for row, sign in vector_a:
                    for column, value in vector_b:
                        matrix[row][column] = (matrix[row][column]
                                               + sign * weight * value) % self.prime
                    self.work.tick("sieve_outer_updates", len(vector_b))
            determinant = _determinant(matrix, self.prime, self.work)
            answer += coefficient * determinant
        return answer % self.prime

    def tree(self):
        if self.impossible:
            return None
        active = set(range(len(self.copies)))
        if len(active) < self.rank or self.evaluate(active) == 0:
            return None
        # Repeated passes are essential: a deletion made later in a pass can
        # change an earlier zero deletion-test into a nonzero test.
        while len(active) > self.rank:
            removed = False
            for index in sorted(active):
                if len(active) == self.rank:
                    break
                self.work.tick("self_reduction_tests")
                if self.evaluate(active - {index}):
                    active.remove(index)
                    removed = True
            if not removed:
                raise ArithmeticError("homogeneous self-reduction invariant failed")
        return sorted(self.copies[index][0] for index in active)


def _solve(problem, *, randomized, max_work, max_histories, seed, prime):
    data = base.normalize(problem)
    work = base.Work(max_work, max_histories)
    method = "triple_sieve" if randomized else "triple_deterministic"
    try:
        failure = base._source_connectivity(data, work)
        if failure:
            return dict(status="NO_FOREST", method=method, certificate=failure,
                        stats=work.export())
        prepared = _prepare(data, work)
        if prepared is None:
            return dict(status="INCONCLUSIVE", method=method,
                        reason="a non-inert column has support greater than three",
                        stats=work.export())
        work.tick("exceptional_columns", len(prepared["triples"]))
        if randomized:
            if not _prime64(prime):
                raise base.InvalidProblem("prime must be prime and smaller than 2**64")
            if seed is not None and type(seed) is not int:
                raise base.InvalidProblem("seed must be an integer or None")
            rng = SystemRandom() if seed is None else Random(seed)
        seen = set()
        for history in _histories(prepared):
            work.tick("search_nodes")
            obligations = _obligations(prepared, history, work)
            if obligations is None or obligations in seen:
                continue
            if len(seen) < 4096:
                seen.add(obligations)
            mandatory, requirements = obligations
            work.tick("distinct_obligations")
            work.counts["maximum_prerequisite_sets"] = max(
                work.counts.get("maximum_prerequisite_sets", 0), len(requirements))
            if not requirements:
                # The k=0 and no-prerequisite cases remain deterministic.
                tree = _forced_cover(data, mandatory, requirements, work)
            elif randomized:
                sieve = CoverageSieve(data, mandatory, requirements, prime, rng, work)
                tree = sieve.tree() if len(mandatory) <= data[0] - 1 else None
            else:
                tree = _forced_cover(data, mandatory, requirements, work)
            if tree is not None:
                certificate = base._positive(data, tree, work)
                return dict(status="SUCCESS", method=method, certificate=certificate,
                            history=[[prepared["triples"][i][0], r] for i, r in history],
                            stats=work.export())
        if randomized:
            return dict(status="INCONCLUSIVE", method=method,
                        reason="no witness found; randomized zero is not a negative certificate",
                        false_negative_bound=dict(numerator=data[0] - 1, denominator=prime),
                        randomness="uniform system randomness" if seed is None else
                        "seeded reproducible experiment; no adversarial probability guarantee",
                        stats=work.export())
        return dict(status="NO_FOREST", method=method,
                    evidence="exhaustive deterministic history and representative search",
                    certificate=None, stats=work.export())
    except base.BudgetExhausted as error:
        return dict(status="INCONCLUSIVE", method=method, reason=str(error),
                    stats=work.export())


def solve(problem, *, max_work=None, max_histories=None):
    """Exact deterministic N**O(k) decision; positive results carry proofs.

    Exhaustive negative answers are algorithmic conclusions, not exported
    compact certificates.  All resource exhaustion returns INCONCLUSIVE.
    """
    return _solve(problem, randomized=False, max_work=max_work,
                  max_histories=max_histories, seed=None, prime=DEFAULT_PRIME)


def solve_randomized(problem, *, max_work=None, max_histories=None,
                     seed=None, prime=DEFAULT_PRIME):
    """One-sided 2**O(k log(k+2))*poly(N) witness search in the stated regime.

    A fixed seed is provided solely for reproducible experiments.  The
    probability theorem assumes independent uniform field samples.
    """
    return _solve(problem, randomized=True, max_work=max_work,
                  max_histories=max_histories, seed=seed, prime=prime)


def main():
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--randomized", action="store_true")
    parser.add_argument("--seed", type=int)
    parser.add_argument("--max-work", type=int)
    parser.add_argument("--max-histories", type=int)
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as stream:
        problem = json.load(stream)
    keywords = dict(max_work=args.max_work, max_histories=args.max_histories)
    result = (solve_randomized(problem, seed=args.seed, **keywords)
              if args.randomized else solve(problem, **keywords))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
