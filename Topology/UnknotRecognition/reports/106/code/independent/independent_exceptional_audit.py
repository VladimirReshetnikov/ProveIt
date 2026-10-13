"""Independent tiny exhaustive oracles for the exceptional-column theorems.

This is a research audit, not a source-authenticating topology checker.
No implementation modules from the incoming package are imported.
"""
from itertools import combinations, permutations, product
import argparse
import json
from pathlib import Path
from random import Random


def trees(vertices, edges):
    rank = vertices - 1
    for chosen in combinations(range(len(edges)), rank):
        parent = list(range(vertices))
        def root(x):
            while parent[x] != x:
                x = parent[x]
            return x
        valid = True
        for e in chosen:
            u, v = edges[e]
            a, b = root(u), root(v)
            if a == b:
                valid = False
                break
            parent[a] = b
        if valid:
            yield frozenset(chosen)


def peels(matrix, removed):
    live = set(range(len(matrix))) - set(removed)
    cols = len(matrix[0]) if matrix else 0
    while live:
        owner = next((next(r for r in live if matrix[r][c])
                      for c in range(cols)
                      if sum(matrix[r][c] for r in live) == 1), None)
        if owner is None:
            return False
        live.remove(owner)
    return True


def ordinary_data(matrix):
    n = len(matrix)
    cols = len(matrix[0]) if matrix else 0
    outgoing = [set() for _ in matrix]
    seeds, triples = set(), []
    for c in range(cols):
        support = [r for r in range(n) if matrix[r][c]]
        if len(support) == 3 and all(matrix[r][c] == 1 for r in support):
            triples.append(tuple(support))
        elif not any(matrix[r][c] == 1 for r in support):
            pass
        elif len(support) == 1:
            seeds.add(support[0])
        elif len(support) == 2:
            u, v = support
            if matrix[u][c] == 1:
                outgoing[v].add(u)
            if matrix[v][c] == 1:
                outgoing[u].add(v)
        else:
            raise ValueError('outside column contract')
    reach = []
    for r in range(n):
        found, stack = {r}, [r]
        while stack:
            u = stack.pop()
            for v in outgoing[u] - found:
                found.add(v)
                stack.append(v)
        reach.append(found)
    groups, seen = [], set()
    for r in range(n):
        if r not in seen:
            group = {u for u in reach[r] if r in reach[u]}
            seen |= group
            if not any(outgoing[u] & group for u in range(n) if u not in group):
                groups.append(group)
    return seeds, triples, reach, groups


def schedule_requirements(matrix):
    seeds, triples, reach, groups = ordinary_data(matrix)
    def closure(rows):
        result = set()
        for r in rows:
            result |= reach[r]
        return result
    for length in range(len(triples) + 1):
        for ordering in permutations(range(len(triples)), length):
            for heads in product(*(triples[i] for i in ordering)):
                prior, arbitrary = set(seeds), []
                for index, head in zip(ordering, heads):
                    reached = closure(prior)
                    for x in triples[index]:
                        if x != head and x not in reached:
                            arbitrary.append({y for y in range(len(matrix)) if x in reach[y]})
                    prior.add(head)
                mandatory = [g for g in groups if not g & prior]
                yield mandatory, arbitrary


def determinant(a, modulus):
    a = [row[:] for row in a]
    result = 1
    for c in range(len(a)):
        pivot = next((r for r in range(c, len(a)) if a[r][c] % modulus), None)
        if pivot is None:
            return 0
        if pivot != c:
            a[pivot], a[c] = a[c], a[pivot]
            result = -result
        v = a[c][c] % modulus
        result = result * v % modulus
        inv = pow(v, -1, modulus)
        for r in range(c + 1, len(a)):
            mul = a[r][c] * inv % modulus
            for j in range(c + 1, len(a)):
                a[r][j] = (a[r][j] - mul * a[c][j]) % modulus
    return result % modulus


class CoverageSieve:
    def __init__(self, vertices, edges, groups, requirements, modulus=101):
        self.rank = vertices - 1
        self.modulus = modulus
        self.edges = edges
        self.groups = groups
        self.requirements = requirements
        self.copies = []
        q = len(groups)
        if q > self.rank:
            raise ValueError('too many groups')
        for edge, (u, v) in enumerate(edges):
            a = [int(i == v) - int(i == u) for i in range(1, vertices)]
            b = [0] * q + [pow(edge + 1, j, modulus) for j in range(self.rank - q)]
            mask = sum(1 << j for j, w in enumerate(requirements) if edge in w)
            self.copies.append((edge, a, b, mask))
            for color, group in enumerate(groups):
                if edge in group:
                    b = [int(i == color) for i in range(q)] + [0] * (self.rank - q)
                    self.copies.append((edge, a, b, mask))
        assert modulus > len(self.copies)

    def value(self, selected, z):
        out = 0
        for missing in range(1 << len(self.requirements)):
            mat = [[0] * self.rank for _ in range(self.rank)]
            for f in selected:
                edge, a, b, mask = self.copies[f]
                if mask & missing:
                    continue
                for i in range(self.rank):
                    for j in range(self.rank):
                        mat[i][j] = (mat[i][j] + z[f] * a[i] * b[j]) % self.modulus
            term = determinant(mat, self.modulus)
            out += (-1 if missing.bit_count() % 2 else 1) * term
        return out % self.modulus

    def expanded_value(self, selected, z):
        result = 0
        for chosen in combinations(selected, self.rank):
            cover = 0
            for f in chosen:
                cover |= self.copies[f][3]
            if cover != (1 << len(self.requirements)) - 1:
                continue
            aa = [[self.copies[f][1][i] for f in chosen] for i in range(self.rank)]
            bb = [[self.copies[f][2][i] for f in chosen] for i in range(self.rank)]
            term = determinant(aa, self.modulus) * determinant(bb, self.modulus)
            for f in chosen:
                term *= z[f]
                term %= self.modulus
            result += term
        return result % self.modulus

    def extract(self, z):
        chosen = set(range(len(self.copies)))
        if not self.value(chosen, z):
            return None
        scans = 0
        while True:
            scans += 1
            changed = False
            for f in sorted(chosen):
                if self.value(chosen - {f}, z):
                    chosen.remove(f)
                    changed = True
            if not changed:
                break
        assert len(chosen) == self.rank
        decoded = {self.copies[f][0] for f in chosen}
        assert len(decoded) == self.rank
        assert all(decoded & g for g in self.groups + self.requirements)
        return decoded, scans


def audit_schedule(rng):
    total_pairs = total_schedules = positive_pairs = 0
    all_k = {}
    for case in range(800):
        n = rng.randint(1, 5)
        m = rng.randint(max(1, n - 1), 7)
        edges = [(i, rng.randrange(i)) for i in range(1, n)]
        edges += [(rng.randrange(n), rng.randrange(n)) for _ in range(m - len(edges))]
        k = rng.randrange(4) if m >= 3 else 0
        columns = []
        for _ in range(k):
            support = rng.sample(range(m), 3)
            columns.append([int(r in support) for r in range(m)])
        for _ in range(rng.randrange(7)):
            support = rng.sample(range(m), rng.randrange(min(2, m) + 1))
            values = [0] * m
            for r in support:
                values[r] = rng.choice([1, 1, 2, 3])
            columns.append(values)
        if rng.randrange(2):
            columns.append([rng.choice([0, 2, 3]) for _ in range(m)])
        matrix = [[column[r] for column in columns] for r in range(m)]
        requirements = list(schedule_requirements(matrix))
        total_schedules += len(requirements)
        all_k[k] = all_k.get(k, 0) + 1
        for tree in trees(n, edges):
            predicted = any(all(tree & group for group in mandatory + arbitrary)
                            for mandatory, arbitrary in requirements)
            actual = peels(matrix, tree)
            assert actual == predicted, (case, tree, matrix)
            total_pairs += 1
            positive_pairs += actual
    return dict(matrix_cases=800, tree_matrix_pairs=total_pairs, schedules_compiled=total_schedules,
                peelable_tree_matrix_pairs=positive_pairs, exceptional_count_histogram=all_k,
                all_exact_equivalences=True)


def audit_sieve(rng):
    feasible = detections = misses = evaluations = 0
    scans = 0
    for case in range(700):
        n = rng.randint(1, 5)
        m = rng.randint(max(1, n - 1), 7)
        edges = [(i, rng.randrange(i)) for i in range(1, n)]
        edges += [(rng.randrange(n), rng.randrange(n)) for _ in range(m - len(edges))]
        q = rng.randrange(n)
        groups = [set() for _ in range(q)]
        for e in range(m):
            color = rng.randrange(q + 1)
            if color < q:
                groups[color].add(e)
        requirements = [{e for e in range(m) if rng.randrange(2)} for _ in range(rng.randrange(4))]
        solutions = [tree for tree in trees(n, edges) if all(tree & g for g in groups + requirements)]
        expected = bool(solutions)
        feasible += expected
        sieve = CoverageSieve(n, edges, groups, requirements)
        detected = False
        for _ in range(3):
            z = [rng.randrange(sieve.modulus) for _ in sieve.copies]
            selected = set(range(len(sieve.copies)))
            value = sieve.value(selected, z)
            assert value == sieve.expanded_value(selected, z)
            evaluations += 1
            if value:
                assert expected
                witness, scan_count = sieve.extract(z)
                assert frozenset(witness) in solutions
                scans = max(scans, scan_count)
                detected = True
                break
        detections += detected
        misses += expected and not detected
    return dict(coverage_cases=700, feasible_cases=feasible, detected_cases=detections,
                three_trial_misses=misses, expanded_polynomial_comparisons=evaluations,
                maximum_extraction_scans=scans, no_false_positive=True,
                all_extracted_witnesses_bruteforce_verified=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'),
                        help='JSON report path (default: beside this script)')
    args = parser.parse_args(argv)
    rng = Random(202610123147)
    result = dict(scope='Independent finite graph/matrix audit; no native topology authentication',
                  seed=202610123147, schedule=audit_schedule(rng), sieve=audit_sieve(rng))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
