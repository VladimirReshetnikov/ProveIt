"""Independent expanded-sheet comparisons for the arithmetic classifier.

The oracle uses graph search for components, parity propagation on the
expanded lifted graph, and direct permutation cycles for boundary lifts.
It calls neither the gcd classifier nor its word evaluator or schema builder.
"""

from collections import Counter, deque
from itertools import permutations, product
import random
import unittest

from dihedral_cover import classify_cover, component_key, boundary_lift_key


def make_input(orientable, genus, boundaries, sheets, monodromy):
    return {
        "surface": {"orientable": orientable, "genus": genus,
                    "boundary_components": boundaries},
        "sheets": sheets,
        "monodromy": [{"sign": sign, "shift": shift} for sign, shift in monodromy],
    }


def expanded_oracle(raw):
    """Return a Counter of component signatures by explicit finite topology."""
    n = raw["sheets"]
    surface = raw["surface"]
    orientable = surface["orientable"]
    genus = surface["genus"]
    boundary_count = surface["boundary_components"]
    maps = [(item["sign"], item["shift"]) for item in raw["monodromy"]]
    crosscap_count = 0 if orientable else genus
    core_generators = 2 * genus if orientable else genus
    signs = [int(index < crosscap_count) for index in range(len(maps))]
    chi_base = 2 - (2 * genus if orientable else genus) - boundary_count

    # Build the lifted spine explicitly, including both directed incidences.
    neighbors = [[] for _ in range(n)]
    for index, (sign, shift) in enumerate(maps):
        for x in range(n):
            y = (sign * x + shift) % n
            neighbors[x].append((y, signs[index]))
            neighbors[y].append((x, signs[index]))

    component_of = [-1] * n
    components = []
    orientation = []
    for x in range(n):
        if component_of[x] >= 0:
            continue
        index = len(components)
        component_of[x] = index
        colors = {x: 0}
        queue = deque([x])
        members = []
        two_coloring = True
        while queue:
            y = queue.popleft()
            members.append(y)
            for z, bit in neighbors[y]:
                expected = colors[y] ^ bit
                if z not in colors:
                    colors[z] = expected
                    component_of[z] = index
                    queue.append(z)
                elif colors[z] != expected:
                    two_coloring = False
        components.append(members)
        orientation.append(two_coloring)

    # Form each boundary permutation directly. The final boundary is the
    # inverse of the product of handle commutators/crosscap squares and
    # boundary generators; no affine word arithmetic is used by this oracle.
    permutations = [[(sign * x + shift) % n for x in range(n)] for sign, shift in maps]
    inverse_permutations = []
    for perm in permutations:
        inverse_perm = [0] * n
        for x, y in enumerate(perm):
            inverse_perm[y] = x
        inverse_permutations.append(inverse_perm)
    relation_steps = []
    if orientable:
        for index in range(0, core_generators, 2):
            relation_steps.extend([permutations[index], permutations[index + 1],
                                   inverse_permutations[index], inverse_permutations[index + 1]])
    else:
        for index in range(core_generators):
            relation_steps.extend([permutations[index], permutations[index]])
    boundary_permutations = list(permutations[core_generators:])
    relation_steps.extend(boundary_permutations)
    final_inverse = [0] * n
    for x in range(n):
        image = x
        for step in relation_steps:
            image = step[image]
        final_inverse[image] = x
    boundary_permutations.append(final_inverse)

    profiles = [[Counter() for _ in range(boundary_count)] for _ in components]
    for boundary, perm in enumerate(boundary_permutations):
        seen = set()
        for x in range(n):
            if x in seen:
                continue
            y, length = x, 0
            while y not in seen:
                seen.add(y)
                if component_of[y] != component_of[x]:
                    raise AssertionError("a boundary cycle crossed cover components")
                y = perm[y]
                length += 1
            if y != x:
                raise AssertionError("the supposed boundary permutation was not bijective")
            profiles[component_of[x]][boundary][length] += 1

    records = Counter()
    for index, members in enumerate(components):
        degree = len(members)
        chi = degree * chi_base
        b = sum(sum(profile.values()) for profile in profiles[index])
        orient = orientation[index]
        genus_numerator = 2 - b - chi
        if orient and (genus_numerator < 0 or genus_numerator % 2):
            raise AssertionError("oracle got impossible orientable Euler data")
        if not orient and genus_numerator < 1:
            raise AssertionError("oracle got impossible nonorientable Euler data")
        genus_cover = genus_numerator // 2 if orient else genus_numerator
        boundary_signature = tuple(tuple(sorted(profile.items())) for profile in profiles[index])
        records[(degree, orient, genus_cover, b, chi, boundary_signature)] += 1
    return records, component_of, boundary_permutations


def compressed_signature(result):
    records = Counter()
    for family in result["families"]:
        profile = tuple(tuple((entry["degree"], entry["multiplicity"]) for entry in entries)
                        for entries in family["boundary_lifts"])
        records[(family["cover_degree"], family["orientable"], family["genus"],
                 family["boundary_components"], family["euler_characteristic"], profile)] += family["multiplicity"]
    return records


class CoverTests(unittest.TestCase):
    comparisons = 0

    def compare(self, raw):
        actual = classify_cover(raw)
        oracle, component_of, boundary_permutations = expanded_oracle(raw)
        self.assertEqual(compressed_signature(actual), oracle, raw)
        self.assertLessEqual(len(actual["families"]), 3)
        self.assertEqual({item["type_id"] for item in actual["families"]},
                         set(range(actual["cover_isomorphism_type_count"])))
        # Check every component identifier without quadratic pair comparisons.
        by_key, by_expanded = {}, {}
        for sheet, expanded in enumerate(component_of):
            key = component_key(actual, sheet)
            self.assertEqual(by_key.setdefault(key, expanded), expanded, raw)
            self.assertEqual(by_expanded.setdefault(expanded, key), key, raw)
        self.assertEqual(actual["component_count"], len(by_key), raw)
        for boundary, permutation in enumerate(boundary_permutations):
            seen, observed_keys = set(), set()
            for sheet in range(raw["sheets"]):
                if sheet in seen:
                    continue
                cycle, x = [], sheet
                while x not in seen:
                    seen.add(x)
                    cycle.append(x)
                    x = permutation[x]
                query = boundary_lift_key(actual, boundary, sheet)
                self.assertNotIn(query["cycle_key"], observed_keys, raw)
                observed_keys.add(query["cycle_key"])
                self.assertEqual(query["covering_degree"], len(cycle), raw)
                self.assertEqual(query["component_key"], component_key(actual, sheet), raw)
                for x in cycle:
                    self.assertEqual(boundary_lift_key(actual, boundary, x), query, raw)
        type(self).comparisons += 1

    def test_all_rank_one_through_40_sheets(self):
        for sheets in range(1, 41):
            for monodromy in product((-1, 1), range(sheets)):
                self.compare(make_input(True, 0, 2, sheets, [monodromy]))
                self.compare(make_input(False, 1, 1, sheets, [monodromy]))

    def test_all_rank_two_through_9_sheets(self):
        schemas = [(True, 1, 1), (True, 0, 3), (False, 2, 1), (False, 1, 2)]
        for sheets in range(1, 10):
            maps = list(product((-1, 1), range(sheets)))
            for monodromy in product(maps, repeat=2):
                for orientable, genus, boundaries in schemas:
                    self.compare(make_input(orientable, genus, boundaries, sheets, monodromy))

    def test_all_rank_three_through_4_sheets(self):
        schemas = [(True, 1, 2), (True, 0, 4), (False, 3, 1), (False, 2, 2), (False, 1, 3)]
        for sheets in range(1, 5):
            maps = list(product((-1, 1), range(sheets)))
            for monodromy in product(maps, repeat=3):
                for orientable, genus, boundaries in schemas:
                    self.compare(make_input(orientable, genus, boundaries, sheets, monodromy))

    def test_seeded_larger_presentations(self):
        rng = random.Random(20261008)
        for _ in range(2000):
            orientable = bool(rng.getrandbits(1))
            genus = rng.randrange(4) if orientable else rng.randrange(1, 5)
            boundaries = rng.randrange(1, 6)
            rank = (2 * genus if orientable else genus) + boundaries - 1
            sheets = rng.randrange(1, 101)
            maps = [(rng.choice((-1, 1)), rng.randrange(-3 * sheets, 3 * sheets + 1))
                    for _ in range(rank)]
            self.compare(make_input(orientable, genus, boundaries, sheets, maps))

    def test_disc_and_huge_multiplicities(self):
        sheets = 1 << 10000
        disc = classify_cover(make_input(True, 0, 1, sheets, []))
        self.assertEqual(disc["component_count"], sheets)
        self.assertEqual(len(disc["families"]), 1)
        self.assertEqual(disc["families"][0]["cover_degree"], 1)
        self.assertEqual(disc["families"][0]["boundary_components"], 1)
        # Reflection over a Mobius-band spine: two fixed Mobius bands and
        # (W-2)/2 annuli, represented by three records even for 2^10000 sheets.
        mobius = classify_cover(make_input(False, 1, 1, sheets, [(-1, 0)]))
        self.assertEqual(mobius["component_count"], sheets // 2 + 1)
        self.assertEqual(len(mobius["families"]), 3)
        paired, fixed0, fixed1 = mobius["families"]
        self.assertTrue(paired["orientable"])
        self.assertEqual(paired["boundary_components"], 2)
        self.assertEqual(paired["multiplicity"], (sheets - 2) // 2)
        self.assertFalse(fixed0["orientable"])
        self.assertFalse(fixed1["orientable"])

    def test_orientation_relations_and_degenerate_actions(self):
        fixtures = [
            # Odd translation order: an orientation-reversing closed lift.
            make_input(False, 1, 1, 9, [(1, 3)]),
            # Even translation order: connected orientable annulus cover.
            make_input(False, 1, 1, 10, [(1, 1)]),
            # Equal permutations with incompatible orientation characters.
            make_input(False, 1, 2, 12, [(1, 2), (1, 2)]),
            # The formal affine signs can coincide as permutations for W<=2.
            make_input(False, 1, 2, 2, [(-1, 0), (1, 1)]),
            make_input(False, 3, 1, 1, [(-1, 0), (1, 0), (-1, 0)]),
            # Reflection residues with different orientability after a twist.
            make_input(False, 1, 2, 8, [(1, 2), (-1, 0)]),
        ]
        for raw in fixtures:
            self.compare(raw)

    def test_relabeling_conjugation(self):
        rng = random.Random(1771)
        for _ in range(300):
            n = rng.randrange(1, 81)
            orient = bool(rng.getrandbits(1))
            g, b = 2, 3
            rank = (2 * g if orient else g) + b - 1
            maps = [(rng.choice((-1, 1)), rng.randrange(n)) for _ in range(rank)]
            gauge_sign, gauge_shift = rng.choice((-1, 1)), rng.randrange(n)
            conjugate = [(sign, (gauge_sign * shift + (1 - sign) * gauge_shift) % n)
                         for sign, shift in maps]
            before = classify_cover(make_input(orient, g, b, n, maps))
            after = classify_cover(make_input(orient, g, b, n, conjugate))
            self.assertEqual(compressed_signature(before), compressed_signature(after))

    def test_generic_cover_equivariance(self):
        for d in range(4, 17):
            for m in range(1, 7):
                n = d * m
                for b0 in (0, 1):
                    maps = [(1, d), (-1, b0), (-1, b0 + 2 * d)]
                    result = classify_cover(make_input(True, 1, 2, n, maps))
                    generic = next(f for f in result["families"]
                                   if f["family"] == "paired-residues")
                    source_residue = generic["representative_component_key"][0]
                    source_key = component_key(result, source_residue)
                    source_sheets = [x for x in range(n)
                                     if component_key(result, x) == source_key]
                    target_keys = {component_key(result, x) for x in range(n)}
                    for target_key in target_keys:
                        if len(target_key) == 1:
                            continue
                        target_residue = target_key[0]

                        def transport(x):
                            if x % d == source_residue:
                                j = (x - source_residue) // d
                                return (target_residue + j * d) % n
                            j = (x - (b0 - source_residue)) // d
                            return (b0 - target_residue + j * d) % n

                        self.assertEqual({transport(x) for x in source_sheets},
                                         {x for x in range(n)
                                          if component_key(result, x) == target_key})
                        for x in source_sheets:
                            for sign, shift in maps:
                                self.assertEqual(transport((sign * x + shift) % n),
                                                 (sign * transport(x) + shift) % n)

    def test_exceptional_cover_isomorphism(self):
        # Exhaust all bijections between the two exceptional sheet orbits.
        # This oracle checks the original permutations directly, without
        # assuming that a commuting bijection has to be a translation.
        for d in (2, 4, 6, 8):
            for m in range(1, 7):
                n = d * m
                for b0 in range(0, d, 2):
                    maps = [(1, d), (-1, b0)]
                    result = classify_cover(make_input(True, 0, 3, n, maps))
                    fixed = [r for r in range(d) if (2 * r - b0) % d == 0]
                    source = [x for x in range(n) if x % d == fixed[0]]
                    target = [x for x in range(n) if x % d == fixed[1]]
                    perms = [[(sign * x + shift) % n for x in range(n)]
                             for sign, shift in maps]
                    found = False
                    for images in permutations(target):
                        candidate = dict(zip(source, images))
                        if all(candidate[perm[x]] == perm[candidate[x]]
                               for perm in perms for x in source):
                            found = True
                            break
                    self.assertEqual(found, bool(m % 2), (d, m, b0))
                    exceptional = [f for f in result["families"]
                                   if f["family"] == "fixed-residue"]
                    self.assertEqual(exceptional[0]["type_id"] == exceptional[1]["type_id"],
                                     found)
                    generic_count = int(any(f["family"] == "paired-residues"
                                            for f in result["families"]))
                    self.assertEqual(result["cover_isomorphism_type_count"],
                                     generic_count + (1 if found else 2))
                    if found:
                        translation = {x: (x + n // 2) % n for x in source}
                        self.assertEqual(set(translation.values()), set(target))
                        self.assertTrue(all(translation[perm[x]] == perm[translation[x]]
                                            for perm in perms for x in source))

        # Small-modulus degeneracies outside the two-fixed-orbit loop.
        for raw in [make_input(True, 0, 1, 1, []),
                    make_input(False, 1, 1, 2, [(-1, 0)]),
                    make_input(False, 1, 1, 2, [(-1, 1)]),
                    make_input(True, 0, 3, 2, [(1, 1), (-1, 0)])]:
            self.assertEqual(classify_cover(raw)["cover_isomorphism_type_count"], 1)

    def test_invalid_inputs(self):
        raw = make_input(True, 0, 2, 7, [(1, 1)])
        mutations = [
            {**raw, "sheets": 0}, {**raw, "sheets": True},
            {**raw, "sheets": 3.0}, {**raw, "extra": 1},
            {**raw, "monodromy": []},
            {**raw, "monodromy": [{"sign": 0, "shift": 1}]},
            {**raw, "monodromy": [{"sign": True, "shift": 1}]},
            {**raw, "monodromy": [{"sign": 1, "shift": "1"}]},
            {**raw, "surface": {"orientable": True, "genus": 1, "boundary_components": 0}},
            {**raw, "surface": {"orientable": False, "genus": 0, "boundary_components": 2}},
            {**raw, "surface": {"orientable": 1, "genus": 0, "boundary_components": 2}},
        ]
        for bad in mutations:
            with self.assertRaises(ValueError):
                classify_cover(bad)
        result = classify_cover(raw)
        for bad_sheet in (-1, 7, True, 2.5):
            with self.assertRaises(ValueError):
                component_key(result, bad_sheet)

    @classmethod
    def tearDownClass(cls):
        print(f"Expanded-sheet topology comparisons: {cls.comparisons}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
