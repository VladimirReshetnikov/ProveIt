"""Independent audit of the special-row Boolean/Mobius determinant filter.

Imports only the independent tiny-matrix oracle module beside this file.
"""
from itertools import combinations
import argparse
import json
from pathlib import Path
from random import Random
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from independent_exceptional_audit import trees, peels, ordinary_data, determinant, CoverageSieve


def special_table(matrix):
    seeds, triples, reach, sources = ordinary_data(matrix)
    special = sorted(set().union(*map(set, triples)) if triples else set())
    index = {r: i for i, r in enumerate(special)}
    full = (1 << len(special)) - 1
    def mask(rows):
        return sum(1 << i for i, r in enumerate(special) if r in rows)
    free = 0
    for row in seeds:
        free |= mask(reach[row])
    ordinary = [mask(reach[row]) for row in special]
    nonlinear = [mask(triple) for triple in triples]
    truth = []
    for initial in range(full + 1):
        current = initial | free
        while True:
            following = current
            for i, dest in enumerate(ordinary):
                if current & (1 << i):
                    following |= dest
            for triple in nonlinear:
                if (current & triple).bit_count() >= 2:
                    following |= triple
            if following == current:
                break
            current = following
        truth.append(int(current == full))
    groups = [s for s in sources if not (s & (seeds | set(special)))]
    ancestors = [{r for r in range(len(matrix)) if u in reach[r]} for u in special]
    return groups, ancestors, truth


class BooleanSieve(CoverageSieve):
    def __init__(self, vertices, edges, groups, ancestors, truth, modulus=101):
        super().__init__(vertices, edges, groups, ancestors, modulus)
        self.truth = truth
        top = len(truth) - 1
        coefficients = [truth[top ^ mask] for mask in range(top + 1)]
        for bit in range(len(ancestors)):
            for mask in range(top + 1):
                if mask & (1 << bit):
                    coefficients[mask] -= coefficients[mask ^ (1 << bit)]
        self.coefficients = coefficients
        # Direct integer inversion audit, before modular arithmetic.
        for mask in range(top + 1):
            subset, total = mask, 0
            while True:
                total += coefficients[subset]
                if subset == 0:
                    break
                subset = (subset - 1) & mask
            assert total == truth[top ^ mask]

    def value(self, selected, z):
        out = 0
        for missing, coefficient in enumerate(self.coefficients):
            if not coefficient:
                continue
            mat = [[0] * self.rank for _ in range(self.rank)]
            for f in selected:
                edge, a, b, mask = self.copies[f]
                if mask & missing:
                    continue
                for i in range(self.rank):
                    for j in range(self.rank):
                        mat[i][j] = (mat[i][j] + z[f] * a[i] * b[j]) % self.modulus
            out += coefficient * determinant(mat, self.modulus)
        return out % self.modulus

    def expanded_value(self, selected, z):
        result = 0
        for chosen in combinations(selected, self.rank):
            cover = 0
            for f in chosen:
                cover |= self.copies[f][3]
            if not self.truth[cover]:
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
        assert all(decoded & g for g in self.groups)
        mask = 0
        for f in chosen:
            mask |= self.copies[f][3]
        assert self.truth[mask]
        return decoded, scans


def audit():
    rng = Random(202610123948)
    checked_pairs = feasible = detections = evaluations = total_table_entries = 0
    group_obstructions = max_t = max_k = max_scans = 0
    for case in range(650):
        vertices = rng.randint(1, 5)
        m = rng.randint(max(1, vertices - 1), 7)
        edges = [(i, rng.randrange(i)) for i in range(1, vertices)]
        edges += [(rng.randrange(vertices), rng.randrange(vertices)) for _ in range(m - len(edges))]
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
        groups, ancestors, truth = special_table(matrix)
        max_t = max(max_t, len(ancestors))
        max_k = max(max_k, k)
        total_table_entries += len(truth)
        solutions = []
        for tree in trees(vertices, edges):
            hitmask = sum(1 << j for j, w in enumerate(ancestors) if tree & w)
            predicted = bool(truth[hitmask] and all(tree & g for g in groups))
            actual = peels(matrix, tree)
            assert predicted == actual, (case, tree, matrix)
            checked_pairs += 1
            if actual:
                solutions.append(tree)
        feasible += bool(solutions)
        if len(groups) > vertices - 1:
            group_obstructions += 1
            assert not solutions
            continue
        sieve = BooleanSieve(vertices, edges, groups, ancestors, truth)
        detected = False
        for _ in range(3):
            z = [rng.randrange(sieve.modulus) for _ in sieve.copies]
            selected = set(range(len(sieve.copies)))
            value = sieve.value(selected, z)
            assert value == sieve.expanded_value(selected, z), case
            evaluations += 1
            if value:
                assert solutions
                witness, scans = sieve.extract(z)
                assert frozenset(witness) in solutions
                max_scans = max(max_scans, scans)
                detected = True
                break
        detections += detected
        assert detected == bool(solutions), ('three-trial false-negative', case)
    return dict(scope='Finite graph/matrix audit; no native topological claims',
                seed=202610123948, matrix_cases=650, tree_matrix_pairs=checked_pairs,
                max_exceptional_columns=max_k, max_special_rows=max_t,
                truth_table_entries=total_table_entries,
                impossible_group_count_cases=group_obstructions,
                feasible_cases=feasible, detected_cases=detections,
                determinant_expansion_comparisons=evaluations,
                maximum_extraction_scans=max_scans,
                all_special_row_closure_equivalences=True,
                all_mobius_inversions_verified_over_integers=True,
                all_extracted_trees_bruteforce_verified=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'),
                        help='JSON report path (default: beside this script)')
    args = parser.parse_args(argv)
    result = audit()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
