import copy
import json
import random
import unittest
from collections import Counter
from unittest.mock import patch

from compiled_ports import Profiles, ProfileRow, ProfileCodec, QuotientEngine, ConeProgram
from compiled_ports.profiles import exact_int, json_safe
from compiled_ports.reference import literal_profiles, literal_components, literal_weighted_backend
from compiled_ports.native import compile_profiles, Inconclusive
from compiled_ports.verify import graph_quotient, verify_quotient, verify_threshold, checked_prefix_blocks, verify_change_points


def set_partitions(n):
    if n == 0:
        yield []
        return
    for previous in set_partitions(n - 1):
        yield previous + [[n - 1]]
        for i in range(len(previous)):
            result = [x[:] for x in previous]
            result[i].append(n - 1)
            yield result


def pairs_for_blocks(blocks):
    return [(block[0], block[0], x, x, False) for block in blocks for x in block[1:]]


def expand(program, node=None, cap=10000):
    node = program.root if node is None else node
    if program.lengths[node] > cap:
        raise ValueError('expanded reference cap')
    n = program.nodes[node]
    if n.op == 'cone':
        return [n.atoms]
    if n.op == 'concat':
        return expand(program, n.left, cap) + expand(program, n.right, cap)
    return expand(program, n.left, cap) * n.exponent


class ProfileTests(unittest.TestCase):
    def test_pack_box_exhaustive(self):
        import itertools
        for lengths in ((1,), (1, 2), (2, 3, 1), (4, 2, 3)):
            for mode in ('binary', 'mixed'):
                codec = ProfileCodec(lengths, mode)
                codes = set()
                for a in itertools.product(*(range(x+1) for x in lengths)):
                    code = codec.encode(a)
                    self.assertEqual(codec.decode(code), a)
                    self.assertNotIn(code, codes)
                    codes.add(code)
                if mode == 'mixed':
                    self.assertEqual(codes, set(range(codec.limit)))

    def test_huge_packing(self):
        lengths = ((1 << 16000), (1 << 9000) + 17, 3)
        for mode in ('binary', 'mixed'):
            codec = ProfileCodec(lengths, mode)
            self.assertEqual(codec.decode(codec.encode(lengths)), lengths)
            self.assertEqual(codec.decode(hex(codec.encode(lengths))), lengths)

    def test_invalid_pack(self):
        codec = ProfileCodec((2,), 'binary')
        for bad in (-1, 3, 4, True, '3', 1.0):
            with self.assertRaises(ValueError):
                codec.decode(bad)
        with self.assertRaises(ValueError):
            codec.encode((3,))

    def test_profile_validation(self):
        for obj in (Profiles.from_histogram((2, 2), {(1, 1): 2}), Profiles((), ())):
            self.assertEqual(Profiles.from_dict(obj.to_dict()), obj)
        invalid = [((2,), (ProfileRow((1,), 1),)),
                   ((2,), (ProfileRow((1,), True),)),
                   ((2,), (ProfileRow((0,), 2),)),
                   ((2,), (ProfileRow((1,), 1), ProfileRow((1,), 1)))]
        for args in invalid:
            with self.assertRaises(ValueError):
                Profiles(*args)

    def test_signed_observation(self):
        table = Profiles.from_histogram((5, 3), {(1, 1): 3, (2, 0): 1})
        self.assertEqual(table.observe([(2, -1), (-3, 5)]), {(-1, 4): 3, (4, -2): 1})

    def test_hex_transport(self):
        table = Profiles.from_histogram((1 << 16000,), {(1,): 1 << 16000})
        text = json.dumps(json_safe(table.to_dict()))
        self.assertEqual(Profiles.from_dict(json.loads(text)), table)
        self.assertRaises(ValueError, exact_int, True)

    def test_literal_compiler_both_packs(self):
        rng = random.Random(26100861)
        for _ in range(500):
            size = rng.randrange(1, 30)
            cuts = [0] + sorted(rng.sample(range(1, size), rng.randrange(min(7, size)))) + [size]
            pairs = []
            for _ in range(rng.randrange(8)):
                width = rng.randrange(1, size + 1)
                a, c = rng.randrange(size-width+1), rng.randrange(size-width+1)
                pairs.append((a, a+width-1, c, c+width-1, bool(rng.randrange(2))))
            expected = literal_profiles(size, pairs, cuts)
            for mode in ('binary', 'mixed'):
                answer = compile_profiles(size, pairs, cuts, packing=mode,
                                          backend=literal_weighted_backend)
                self.assertEqual(answer['profiles'], expected)

    def test_compiler_incomplete_and_validation(self):
        self.assertRaises(Inconclusive, compile_profiles, 1, [], [0, 1],
                          backend=lambda *a, **k: {'status': 'INCONCLUSIVE'})
        for bad in ([0, 0, 1], [1], [0, 2]):
            self.assertRaises(ValueError, compile_profiles, 1, [], bad,
                              backend=literal_weighted_backend)
        self.assertRaises(ValueError, compile_profiles, 1, [], [0, 1],
                          record_certificate=True, backend=literal_weighted_backend)
        table = compile_profiles(0, [], [0], backend=literal_weighted_backend)['profiles']
        self.assertEqual(table, Profiles((), ()))

    def test_false_valued_callback(self):
        class Cancel:
            def __bool__(self): return False
            def __call__(self): raise RuntimeError('cancelled')
        self.assertRaisesRegex(RuntimeError, 'cancelled', compile_profiles,
                               1, [], [0, 1], check=Cancel(), backend=literal_weighted_backend)


class QuotientTests(unittest.TestCase):
    def test_exhaustive_partitions_and_one_cone(self):
        self.cases = 0
        for n in range(1, 6):
            for partition in set_partitions(n):
                pairs = pairs_for_blocks(partition)
                for mask in range(1 << (n-1)):
                    cuts = [0] + [x for x in range(1, n) if mask >> (x-1) & 1] + [n]
                    table = literal_profiles(n, pairs, cuts)
                    m = len(cuts) - 1
                    for cone_mask in range(1 << m):
                        cone = [j for j in range(m) if cone_mask >> j & 1]
                        state = QuotientEngine(table)
                        state.cone(cone)
                        expected = literal_profiles(n, pairs, cuts, cones=[cone])
                        self.assertEqual(state.census(), expected)
                        self.assertTrue(verify_quotient(table, [cone], expected))
                        self.cases += 1
        self.assertGreater(self.cases, 9000)

    def test_random_sequences_and_reuse(self):
        rng = random.Random(26100862)
        for _ in range(700):
            n = rng.randrange(1, 35)
            cuts = [0] + sorted(rng.sample(range(1, n), rng.randrange(min(n, 7)))) + [n]
            pairs = []
            for _ in range(rng.randrange(8)):
                a, b = rng.randrange(n), rng.randrange(n)
                pairs.append((a, a, b, b, False))
            table = literal_profiles(n, pairs, cuts)
            state, cones = QuotientEngine(table), []
            for _ in range(10):
                group = rng.sample(range(len(cuts)-1), rng.randrange(len(cuts)))
                cones.append(group)
                state.cone(group)
                expected = literal_profiles(n, pairs, cuts, cones=cones)
                self.assertEqual(state.census(), expected)
                self.assertEqual(graph_quotient(table, cones), expected)
            self.assertLessEqual(state.stats['incidence_edges'], table.edges)
            self.assertLessEqual(state.stats['activated_types'], len(table.rows))

    def test_huge_parallel_population(self):
        q = 1 << 16000
        table = Profiles.from_histogram((q,) * 64, {(1,) * 64: q})
        state = QuotientEngine(table)
        self.assertEqual(state.count, q)
        self.assertEqual(state.cone([31]), 1)
        self.assertEqual(state.cone([0, 63]), 1)
        self.assertEqual(state.census().rows, (ProfileRow((q,) * 64, 1),))

    def test_clone_isolation(self):
        table = Profiles.from_histogram((4, 4), {(1, 0): 4, (0, 1): 4})
        a, b = QuotientEngine(table), QuotientEngine(table)
        c = a.clone()
        c.cone([0, 1])
        self.assertEqual(a.count, 8)
        self.assertEqual(c.count, 1)
        self.assertEqual(a.census(), b.census())

    def test_invalid_update_is_transactional(self):
        table = Profiles.from_histogram((2, 2), {(1, 1): 2})
        state = QuotientEngine(table)
        for bad in ([True], [-1], [2], [0, '1']):
            self.assertRaises(ValueError, state.cone, bad)
            self.assertEqual(state.count, 2)
        self.assertRaises(ValueError, state.apply_blocks, [[0], [2]])
        self.assertEqual(state.count, 2)

    def test_commutation_idempotence(self):
        table = Profiles.from_histogram((5, 3, 4), {(1, 1, 0): 3, (1, 0, 2): 2})
        cones = [[0], [1, 2], []]
        a = graph_quotient(table, cones)
        b = graph_quotient(table, list(reversed(cones)) + cones * 3)
        self.assertEqual(a, b)

    def test_partial_attachment_counterexample(self):
        p = [(0, 0, 2, 2, False), (1, 1, 3, 3, False)]
        q = [(0, 0, 3, 3, False), (1, 1, 2, 2, False)]
        self.assertEqual(literal_profiles(4, p, [0, 2, 4]), literal_profiles(4, q, [0, 2, 4]))
        extra = [(0, 0, 2, 2, False)]
        self.assertEqual(len(literal_components(4, p + extra)), 2)
        self.assertEqual(len(literal_components(4, q + extra)), 1)

    def test_verifier_independent_of_engine(self):
        table = Profiles.from_histogram((3, 3), {(1, 1): 3})
        claimed = graph_quotient(table, [[0]])
        with patch.object(QuotientEngine, 'cone', side_effect=AssertionError('producer called')):
            self.assertTrue(verify_quotient(table, [[0]], claimed))
        self.assertFalse(verify_quotient(table, [], claimed))


class ProgramTests(unittest.TestCase):
    def test_random_grammars_every_prefix_and_threshold(self):
        rng = random.Random(26100863)
        for _ in range(400):
            m = rng.randrange(1, 7)
            hist = {tuple(int(j == i) for j in range(m)): rng.randrange(1, 6) for i in range(m)}
            table = Profiles.from_histogram(tuple(hist[tuple(int(j == i) for j in range(m))]
                                                    for i in range(m)), hist)
            nodes = [dict(op='cone', atoms=rng.sample(range(m), rng.randrange(m+1)))]
            lengths = [1]
            for i in range(1, 12):
                op = rng.randrange(3)
                if op == 0:
                    nodes.append(dict(op='cone', atoms=rng.sample(range(m), rng.randrange(m+1))))
                    lengths.append(1)
                elif op == 1:
                    a, b = rng.randrange(i), rng.randrange(i)
                    nodes.append(dict(op='concat', left=a, right=b))
                    lengths.append(lengths[a] + lengths[b])
                else:
                    a, power = rng.randrange(i), rng.randrange(4)
                    nodes.append(dict(op='power', child=a, exponent=power))
                    lengths.append(lengths[a] * power)
            prog = ConeProgram(m, nodes)
            expanded = expand(prog)
            reference = QuotientEngine(table)
            counts = [reference.count]
            for j, cone in enumerate(expanded, 1):
                reference.cone(cone)
                counts.append(reference.count)
                self.assertEqual(prog.evaluate(table, j).census(), reference.census())
                blocks = checked_prefix_blocks(m, nodes, prog.root, j)
                self.assertEqual(graph_quotient(table, blocks), reference.census())
            actual_events = [dict(index=i, before=counts[i-1], after=counts[i])
                             for i in range(1, len(counts)) if counts[i] < counts[i-1]]
            compressed_events = prog.change_points(table)
            self.assertEqual(compressed_events['events'], actual_events)
            self.assertLessEqual(len(actual_events), 2*m-1)
            self.assertTrue(verify_change_points(table, nodes, prog.root, actual_events))
            for target in range(0, table.orbit_count + 2):
                expected = next((i for i, c in enumerate(counts) if c <= target), None)
                answer = prog.first_at_most(table, target)
                self.assertEqual(answer['index'], expected)
                self.assertLessEqual(answer['trials'], len(nodes) + 1)
                self.assertTrue(verify_threshold(table, nodes, prog.root, target, expected))

    def test_huge_delayed_threshold(self):
        q, delay = 1 << 2048, 1 << 16000
        table = Profiles.from_histogram((q,) * 8, {(1,) * 8: q})
        nodes = [dict(op='cone', atoms=[]), dict(op='power', child=0, exponent=delay),
                 dict(op='cone', atoms=[2]), dict(op='concat', left=1, right=2),
                 dict(op='power', child=3, exponent=1 << 12000)]
        prog = ConeProgram(8, nodes)
        answer = prog.first_at_most(table, 1)
        self.assertEqual(answer['index'], delay + 1)
        self.assertEqual(answer['trials'], 2)
        self.assertTrue(verify_threshold(table, nodes, 4, 1, delay + 1))
        self.assertFalse(verify_threshold(table, nodes, 4, 1, delay + 2))
        self.assertEqual(prog.evaluate(table, delay).count, q)
        self.assertEqual(prog.evaluate(table, delay + 1).count, 1)

    def test_empty_program_and_zero_universe(self):
        prog = ConeProgram(0, [dict(op='cone', atoms=[]), dict(op='power', child=0, exponent=0)])
        self.assertEqual(prog.length, 0)
        self.assertEqual(prog.evaluate(Profiles((), ())).count, 0)
        self.assertEqual(prog.first_at_most(Profiles((), ()), -1)['index'], None)
        self.assertEqual(prog.first_at_most(Profiles((), ()), 0)['index'], 0)

    def test_bad_programs(self):
        invalid = [[], [dict(op='power', child=0, exponent=2)],
                   [dict(op='cone', atoms=[True])], [dict(op='cone', atoms=[3])],
                   [dict(op='cone', atoms=[]), dict(op='power', child=0, exponent=-1)],
                   [dict(op='cone', atoms=[], extra=0)]]
        for nodes in invalid:
            self.assertRaises(ValueError, ConeProgram, 2, nodes)

    def test_independent_threshold_and_mutations(self):
        table = Profiles.from_histogram((3, 3), {(1, 1): 3})
        records = [dict(op='cone', atoms=[]), dict(op='cone', atoms=[0]),
                   dict(op='concat', left=0, right=1)]
        with patch.object(ConeProgram, 'prefix_summary', side_effect=AssertionError('producer')):
            self.assertTrue(verify_threshold(table, records, 2, 1, 2))
        for wrong in (None, 0, 1, 3, True):
            self.assertFalse(verify_threshold(table, records, 2, 1, wrong))
        altered = copy.deepcopy(records)
        altered[1]['atoms'] = []
        self.assertFalse(verify_threshold(table, altered, 2, 1, 2))

    def test_sharp_height_and_huge_plateaux(self):
        for m in range(1, 17):
            table = Profiles.from_histogram((2,)*m,
                {tuple(int(j == i) for j in range(m)): 2 for i in range(m)})
            sequence = [[i] for i in range(m)] + [[0, i] for i in range(1, m)]
            records = [dict(op='cone', atoms=[]),
                       dict(op='power', child=0, exponent=1 << 2048)]
            root = 1
            for group in sequence:
                records.append(dict(op='cone', atoms=group))
                leaf = len(records)-1
                records.append(dict(op='concat', left=root, right=leaf))
                root = len(records)-1
                records.append(dict(op='concat', left=root, right=1))
                root = len(records)-1
            records.append(dict(op='power', child=root, exponent=1 << 4096))
            program = ConeProgram(m, records)
            result = program.change_points(table)
            self.assertEqual(len(result['events']), 2*m-1)
            self.assertEqual(result['count'], 1)
            self.assertTrue(verify_change_points(table, records, program.root, result['events']))
            self.assertFalse(verify_change_points(table, records, program.root, result['events'][:-1]))
            self.assertFalse(verify_change_points(table, records, program.root, result['events'][1:]))

    def test_event_verifier_producer_disabled(self):
        table = Profiles.from_histogram((2,), {(1,): 2})
        records = [dict(op='cone', atoms=[0])]
        events = [dict(index=1, before=2, after=1)]
        with patch.object(ConeProgram, 'change_points', side_effect=AssertionError('producer')):
            with patch.object(QuotientEngine, 'cone', side_effect=AssertionError('producer')):
                self.assertTrue(verify_change_points(table, records, 0, events))
        for bad in [[], [dict(index=0, before=2, after=1)],
                    [dict(index=1, before=2, after=0)],
                    [dict(index=True, before=2, after=1)]]:
            self.assertFalse(verify_change_points(table, records, 0, bad))

    def test_deep_iterative_grammar(self):
        nodes = [dict(op='cone', atoms=[0])]
        for i in range(1, 2500):
            nodes.append(dict(op='power', child=i-1, exponent=2))
        prog = ConeProgram(1, nodes)
        table = Profiles.from_histogram((5,), {(1,): 5})
        self.assertEqual(prog.first_at_most(table, 1)['index'], 1)
        self.assertEqual(prog.evaluate(table, 1).count, 1)


if __name__ == '__main__':
    unittest.main()
