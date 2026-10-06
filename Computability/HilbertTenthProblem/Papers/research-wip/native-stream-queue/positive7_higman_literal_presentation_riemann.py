#!/usr/bin/env python3
"""ORIGINAL literal-word constructor. UNRUN; root must preflight before sole run.

Only immutable proof bytes and explicit finite word recipes are consumed. There
is no parser/evaluator for scientific arrays, no group reduction, no simulation,
no coefficient specialization, and no degree propagation. Every word is a flat
signed-generator tuple; cancellation is deliberately absent. This stops at the
preembedding benign pair. It does not implement Mikaelian Section 7.
"""
from pathlib import Path
import hashlib
import json
import subprocess

REPO = Path('/home/codex/.codex/worktrees/2a71/Proofs')
BASE = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
COMMIT = '81315a6b3a408880fdd04bc5754cf69991c0ba40'
OUTPUT = Path('/tmp/positive7_higman_literal_presentation_riemann.json')
DEPENDENCIES = (
    ('positive7_higman_benign_recipes_aristotle.md', '826c85fe63f3c2cd8f9df2b43efa3f4a7fc098db5552bbf494d41e5c0150c07c', '4bae002fb8879093192b956c6f57755b7a93898f'),
    ('positive7_higman_shared_ambient_aristotle.md', '12692f7c9037bef148e7a9cb7788c78465745b797889ebed4098da415b24c562', '73f3f9c0bf31f7a60124e317140bac09d2b7b571'),
    ('positive7_higman_shared_schedule_riemann.md', 'b06d3356c9960604580e3f31eae64641b35dda7129560c43764dea8ad9019526', 'd48ae47879f116bdf58180c77da0dd3f88ed603a'),
    ('positive7_affine_typed_recognizer_pascal.md', '78e26e7b637378c5568a7da1127f5b39996572d3f254c3a65bf0065ffb61fcd0', 'a30a70cea179b6194b5facdf50353fc4067d49c9'),
    ('positive7_higman_affine_line_transducer_aristotle.md', 'e431ab657885f06502be8685cbdd2cef92fe65c75e3d8692b8302aac355dc42f', '22732da84a880ec83a3de3d26c6c3d9a853b4829'),
)
A_ROLES = ('a', 'b', 'c', 't', 't_prime', 'u1', 'u2', 'd', 'e')


def digest_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def record_hash(record):
    return digest_bytes(json.dumps(record, separators=(',', ':'), ensure_ascii=True).encode())


def inv(word):
    return tuple(-letter for letter in reversed(word))


def power(word, exponent):
    assert type(exponent) is int
    return (word if exponent >= 0 else inv(word)) * abs(exponent)


def conjugate(word, by):
    return inv(by) + word + by


def concatenate(words):
    return tuple(letter for word in words for letter in word)


def shifted_letter(base, shift, index):
    return conjugate(base, power(shift, index))


def vector_word(base, shift, vector):
    # The vector is an explicit original finite spelling prescription, not a
    # supplied scientific record to execute. Zero powers append the empty word.
    assert [i for i, exponent in vector] == sorted(i for i, exponent in vector)
    assert len({i for i, exponent in vector}) == len(vector)
    return concatenate(power(shifted_letter(base, shift, i), exponent)
                       for i, exponent in vector)


def immutable_dependencies():
    records = []
    for filename, expected_sha, expected_blob in DEPENDENCIES:
        path = BASE + filename
        ref = COMMIT + ':' + path
        raw = subprocess.check_output(['git', 'show', ref], cwd=REPO)
        blob = subprocess.check_output(['git', 'rev-parse', ref], cwd=REPO, text=True).strip()
        assert digest_bytes(raw) == expected_sha and blob == expected_blob
        records.append({'path': path, 'commit': COMMIT, 'git_blob': blob,
                        'sha256': expected_sha, 'bytes': len(raw),
                        'LF_lines': raw.count(b'\n')})
    return records


class LiteralPresentation:
    def __init__(self):
        self.generators = []
        self.relators = []
        self.cache = {}
        self.marker = ()
        self.tracked_A = {}
        self.shift = ()
        self.events = []
        self.active = None

    def state(self):
        return {'g': len(self.generators), 'r': len(self.relators),
                'marker_ids': self.marker, 'tracked_A': dict(self.tracked_A),
                'global_shift_word': self.shift,
                'cache_fingerprints': [
                    {'name': name, 'length': len(words), 'sha256': record_hash(words)}
                    for name, words in self.cache.items()]}

    def begin(self, label, kind, inputs=(), detail=None):
        assert self.active is None and label not in [e['label'] for e in self.events]
        assert all(name in self.cache for name in inputs)
        self.active = {'id': len(self.events) + 1, 'label': label, 'kind': kind,
                       'inputs': list(inputs), 'detail': detail or {},
                       'before': self.state(), 'created_cache_names': []}

    def finish(self, selected=None, expected=None):
        event = self.active
        assert event is not None
        after = self.state()
        if expected is not None:
            assert selected is not None
            assert (after['g'], after['r'], len(self.cache[selected])) == expected
        event['after'] = after
        event['selected'] = selected
        event['new_generator_ids'] = list(range(event['before']['g'] + 1, after['g'] + 1))
        event['relator_interval'] = [event['before']['r'], after['r']]
        event['created_lists'] = {name: self.cache[name] for name in event.pop('created_cache_names')}
        event['asserted_checkpoint'] = expected
        self.events.append(event)
        self.active = None

    def new(self, role):
        assert self.active is not None
        name = self.active['label'] + '/' + role
        assert all(row['name'] != name for row in self.generators)
        identifier = len(self.generators) + 1
        self.generators.append({'id': identifier, 'name': name,
                                'event': self.active['id'],
                                'declared_after_relator': len(self.relators)})
        return (identifier,)

    def valid_word(self, word):
        assert isinstance(word, tuple)
        assert all(type(k) is int and k != 0 and abs(k) <= len(self.generators) for k in word)

    def equation(self, family, stable, source, target):
        assert len(stable) == 1 and stable[0] > 0
        for word in (stable, source, target):
            self.valid_word(word)
        relator = inv(stable) + source + stable + inv(target)
        self.relators.append({'index': len(self.relators), 'event': self.active['id'],
                              'family': family, 'stable': stable,
                              'source': source, 'target': target, 'word': relator})

    def fix_existing(self, family, stable, words):
        for index, word in enumerate(words):
            self.equation(family + '/' + str(index), stable, word, word)

    def fix(self, role, words):
        stable = self.new(role)
        self.fix_existing(role, stable, words)
        return stable

    def mapping(self, role, sources, targets):
        assert len(sources) == len(targets)
        stable = self.new(role)
        for index, (source, target) in enumerate(zip(sources, targets)):
            self.equation(role + '/' + str(index), stable, source, target)
        return stable

    def cache_list(self, name, words):
        assert name not in self.cache
        words = tuple(words)
        for word in words:
            self.valid_word(word)
        self.cache[name] = words
        self.active['created_cache_names'].append(name)

    def marker_words(self):
        return tuple((identifier,) for identifier in self.marker)

    def attach_A(self, role, shared_marker=None):
        begin_g, begin_r = len(self.generators), len(self.relators)
        a = {}
        if shared_marker is not None:
            assert len(shared_marker) == 3
            for key, word in zip(A_ROLES[:3], shared_marker):
                assert len(word) == 1
                a[key] = word
        for key in A_ROLES:
            if key not in a:
                a[key] = self.new(role + '/' + key)
        b, c, t, tp = (a[key] for key in ('b', 'c', 't', 't_prime'))
        self.equation(role + '/b_t', t, b, b)
        self.equation(role + '/b_t_prime', tp, b, conjugate(b, inv(c)))
        self.equation(role + '/c_t', t, c, power(c, 2))
        self.equation(role + '/c_t_prime', tp, c, power(c, 2))
        self.fix_existing(role + '/u1', a['u1'], (conjugate(b, c), t, tp))
        self.fix_existing(role + '/u2', a['u2'], (a['a'], b, t, tp))
        markers = (a['a'], b, c)
        self.fix_existing(role + '/d_fixed', a['d'], tuple(conjugate(x, a['u1']) for x in markers))
        sources = tuple(conjugate(x, a['u2']) for x in markers)
        targets = (conjugate(a['a'], b + a['u2']), conjugate(b, a['u2']),
                   conjugate(c, b + a['u2']))
        for index, (source, target) in enumerate(zip(sources, targets)):
            self.equation(role + '/d_map/' + str(index), a['d'], source, target)
        for index, (source, target) in enumerate(zip(markers, (a['a'], conjugate(b, c), c))):
            self.equation(role + '/e/' + str(index), a['e'], source, target)
        assert len(self.generators) - begin_g == (9 if shared_marker is None else 6)
        assert len(self.relators) - begin_r == 20
        return a

    def initialize(self):
        self.begin('initial', 'A_and_global_shift')
        a = self.attach_A('A')
        self.marker = tuple(a[key][0] for key in ('a', 'b', 'c'))
        self.tracked_A = dict(a)
        self.shift = self.mapping('global_s', self.marker_words(),
                                  (a['a'], conjugate(a['b'], a['c']), a['c']))
        self.finish()
        assert (len(self.generators), len(self.relators)) == (10, 23)

    def affine(self, name, offset, directions, description):
        self.begin(name, 'affine_leaf', detail={'offset': offset, 'directions': directions,
                                              'description': description,
                                              'basis': 'literal tracked_A images'})
        a = self.tracked_A
        anchor = conjugate(a['a'], vector_word(a['b'], a['c'], offset))
        words = (anchor,) + tuple(vector_word(a['d'], a['e'], vector) for vector in directions)
        self.cache_list(name, words)
        self.finish(name)

    def shift_list(self, name, source, exponent):
        self.begin(name, 'fixed_shift', (source,), {'exponent': exponent})
        by = power(self.shift, exponent)
        self.active['detail']['conjugator'] = by
        self.cache_list(name, tuple(conjugate(word, by) for word in self.cache[source]))
        self.finish(name)

    def binary(self, name, left, right, union, expected=None):
        self.begin(name, 'union' if union else 'intersection', (left, right))
        before_g, before_r = len(self.generators), len(self.relators)
        left_words, right_words = self.cache[left], self.cache[right]
        v1 = self.fix('v1', left_words)
        v2 = self.fix('v2', right_words)
        marker = self.marker_words()
        if union:
            result = tuple(conjugate(w, v1) for w in marker) + tuple(conjugate(w, v2) for w in marker)
        else:
            result = tuple(conjugate(w, v1 + v2) for w in marker)
        self.cache_list(name, result)
        assert len(self.generators) == before_g + 2
        assert len(self.relators) == before_r + len(left_words) + len(right_words)
        self.finish(name, expected)

    def transport(self, old_marker, new_marker):
        assert self.marker_words() == old_marker
        old_names = tuple(self.cache)
        stable = self.mapping('persistent_transport', old_marker, new_marker)
        for name in old_names:
            self.cache[name] = tuple(conjugate(w, stable) for w in self.cache[name])
        self.tracked_A = {key: conjugate(word, stable) for key, word in self.tracked_A.items()}
        self.shift = conjugate(self.shift, stable)
        self.marker = tuple(word[0] for word in new_marker)
        self.active['detail']['persistent_transport'] = {
            'stable': stable, 'old_marker': old_marker, 'new_marker': new_marker,
            'transported_cache_names': old_names,
            'tracked_A_rule': 'conjugate all nine literal words; no marker-alias substitution',
            'new_output_excluded': True}

    def rho(self, name, source, expected):
        self.begin(name, 'rho', (source,))
        before_g, before_r = len(self.generators), len(self.relators)
        selected = self.cache[source]
        old_marker = self.marker_words()
        barred = self.attach_A('bar_A', old_marker)
        left_ids = tuple(range(1, len(self.generators) + 1))
        fresh = self.attach_A('fresh_A')
        right_words = tuple(fresh[key] for key in A_ROLES)
        for identifier in left_ids:
            for index, right in enumerate(right_words):
                self.equation('direct_product/' + str(identifier) + '/' + str(index),
                              (identifier,), right, right)
        v1 = self.fix('v1', (barred['a'] + fresh['a'], barred['d'] + fresh['d'],
                              barred['e'] + inv(fresh['e'])))
        v2 = self.fix('v2', selected + (fresh['a'], fresh['d'], fresh['e']))
        graph_base = tuple(barred[key] for key in A_ROLES) + right_words
        graph = tuple(conjugate(word, v1 + v2) for word in graph_base)
        new_marker = tuple(fresh[key] for key in ('a', 'b', 'c'))
        c6 = new_marker + old_marker
        w1 = self.fix('w1', old_marker)
        w2 = self.fix('w2', graph)
        w3 = self.fix('w3', new_marker)
        self.fix('w4', tuple(conjugate(w, w1) for w in c6) + tuple(conjugate(w, w2) for w in c6))
        w4 = (len(self.generators),)
        result = tuple(conjugate(w, w3 + w4) for w in c6)
        self.active['detail'].update({'input_role_aliases': dict(zip(('abar', 'bbar', 'cbar'), old_marker)),
                                      'bar_A': barred, 'fresh_A': fresh, 'product_left_ids': left_ids,
                                      'graph_base': graph_base, 'graph_list': graph, 'C6': c6})
        self.transport(old_marker, new_marker)
        self.cache_list(name, result)
        assert len(self.generators) == before_g + 22
        assert len(self.relators) == before_r + 9 * before_g + len(selected) + 139
        self.finish(name, expected)

    def pi(self, name, source, expected):
        self.begin(name, 'pi', (source,))
        before_g, before_r = len(self.generators), len(self.relators)
        selected = self.cache[source]
        a = self.attach_A('A_star', self.marker_words())
        x = self.mapping('x', (a['d'], a['e']), (a['d'], power(a['e'], 2)))
        xp = self.mapping('x_prime', (a['d'], a['e']),
                          (shifted_letter(a['d'], a['e'], -1), power(a['e'], 2)))
        base = tuple((identifier,) for identifier in range(1, len(self.generators) + 1))
        v1 = self.fix('v1', selected)
        v2 = self.fix('v2', (shifted_letter(a['d'], a['e'], 1), x, xp))
        v3 = self.fix('v3', tuple(conjugate(w, v1) for w in base) + tuple(conjugate(w, v2) for w in base))
        v4 = self.fix('v4', self.marker_words())
        self.cache_list(name, tuple(conjugate(w, v3 + v4) for w in base))
        self.active['detail'].update({'A_star_A': a, 'X_B': base, 'x': x, 'x_prime': xp})
        assert len(base) == before_g + 8
        assert len(self.generators) == before_g + 12
        assert len(self.relators) == before_r + 2 * before_g + len(selected) + 46
        self.finish(name, expected)

    def omega(self, name, source, block, zero_witness, expected):
        assert block in (1, 2, 18)
        self.begin(name, 'omega', (source,), {'block': block, 'zero_block_witness': zero_witness})
        before_g, before_r = len(self.generators), len(self.relators)
        selected = self.cache[source]
        old_marker = self.marker_words()
        fixed = {key: self.new('D/' + key) for key in
                 ('b', 'c', 't_d', 't_d_prime', 't_0', 't_0_prime', 'r1', 'r2')}
        b, c = fixed['b'], fixed['c']
        for key, offset in (('t_d', 1 - block), ('t_d_prime', -block), ('t_0', 1), ('t_0_prime', 0)):
            self.equation('D/' + key + '/b', fixed[key], b, shifted_letter(b, c, offset))
            self.equation('D/' + key + '/c', fixed[key], c, power(c, 2))
        self.fix_existing('D/r1', fixed['r1'], (shifted_letter(b, c, block), fixed['t_d'], fixed['t_d_prime']))
        self.fix_existing('D/r2', fixed['r2'], (shifted_letter(b, c, -1), fixed['t_0'], fixed['t_0_prime']))
        g0, h, k = old_marker
        z_fixed = (conjugate(b, fixed['r1']), conjugate(c, fixed['r1']),
                   conjugate(b, fixed['r2']), conjugate(c, fixed['r2']))
        for role, stable in zip(('g0', 'h', 'k'), old_marker):
            self.fix_existing('D/' + role, stable, z_fixed)
        X_G = tuple(fixed.values()) + old_marker
        assert len(X_G) == 11 and len(self.relators) == before_r + 26
        lambdas = []
        for s in range(1, block + 1):
            row = []
            hi = tuple(shifted_letter(h, k, i) for i in range(s))
            for j in range(s):
                source_words = (shifted_letter(b, c, s - 1), g0) + hi
                target_words = (source_words[0], conjugate(g0, hi[j])) + tuple(
                    conjugate(word, hi[j]) if i < j else word for i, word in enumerate(hi))
                row.append(self.mapping('D/lambda_' + str(s - 1) + '_' + str(j), source_words, target_words))
            lambdas.append(tuple(row))
        ps = [self.fix('D/p0', (g0,))]
        for s, row in enumerate(lambdas, 1):
            special = conjugate(g0, shifted_letter(h, k, s - 1)) + inv(shifted_letter(b, c, s - 1)) + inv(g0)
            ps.append(self.fix('D/p' + str(s), (special,) + row))
        new_a = self.fix('D/a', tuple(conjugate(word, stable) for stable in ps for word in X_G))
        new_marker = (new_a, b, c)
        q = self.mapping('D/q', new_marker, (new_a, conjugate(b, power(c, block)), c))
        X_D = X_G + tuple(word for row in lambdas for word in row) + tuple(ps) + (new_a, q)
        fixed_census = {1: (16, 57), 2: (19, 79), 18: (203, 2879)}
        assert (len(X_D), len(self.relators) - before_r) == fixed_census[block]
        assert len({word[0] for word in X_D}) == len(X_D)
        q1 = self.fix('q1', selected)
        q2 = self.fix('q2', (new_a, q))
        q3 = self.fix('q3', tuple(conjugate(word, q1) for word in X_D) + tuple(conjugate(word, q2) for word in X_D))
        q4 = self.fix('q4', new_marker)
        result = tuple(conjugate(word, q3 + q4) for word in X_D)
        self.active['detail'].update({'input_role_aliases': dict(zip(('g0', 'h', 'k'), old_marker)),
                                      'X_G': X_G, 'lambda_rows': lambdas, 'p_letters': ps,
                                      'X_D': X_D, 'new_marker': new_marker})
        self.transport(old_marker, new_marker)
        self.cache_list(name, result)
        assert len(self.generators) == before_g + {1: 18, 2: 21, 18: 205}[block]
        assert len(self.relators) == before_r + len(selected) + {1: 97, 2: 125, 18: 3293}[block]
        self.finish(name, expected)

    def transducer(self):
        self.begin('X_U', 'two_relator_affine_line_transducer', ('Accepted',))
        a, b, c = self.marker_words()
        alpha = conjugate(a, power(b, 23))
        beta = conjugate(b, c)
        offset = ((2, 1), (4, 1), (6, -1), (8, -1))
        direction = ((1, -1), (3, 1), (5, -1), (7, 1))
        anchor = conjugate(a, vector_word(b, c, offset))
        by = vector_word(self.tracked_A['d'], self.tracked_A['e'], direction)
        t = self.mapping('t', (alpha, beta), (anchor, by))
        self.cache_list('X_U', tuple(conjugate(word, t) for word in self.cache['Accepted']))
        self.active['detail'].update({'alpha': alpha, 'beta': beta, 'target_anchor': anchor,
                                      'target_direction_word': by, 'target_offset': offset,
                                      'target_direction': direction, 'stable': t,
                                      'no_marker_cache_A_or_shift_transport': True})
        self.finish('X_U', (499, 17678, 3))

    def final_syntax_audit(self):
        assert self.active is None
        assert [row['id'] for row in self.generators] == list(range(1, 500))
        assert len({row['name'] for row in self.generators}) == 499
        assert [row['index'] for row in self.relators] == list(range(17678))
        for row in self.relators:
            for field in ('stable', 'source', 'target', 'word'):
                self.valid_word(row[field])
            assert row['word'] == inv(row['stable']) + row['source'] + row['stable'] + inv(row['target'])
        for words in self.cache.values():
            for word in words:
                self.valid_word(word)
        for word in self.tracked_A.values():
            self.valid_word(word)
        self.valid_word(self.shift)
        assert len(self.cache['X_U']) == 3
        next_generator, next_relator = 1, 0
        for event in self.events:
            assert event['new_generator_ids'] == list(range(next_generator, event['after']['g'] + 1))
            assert event['relator_interval'] == [next_relator, event['after']['r']]
            assert all(row['event'] == event['id'] for row in self.relators[next_relator:event['after']['r']])
            next_generator, next_relator = event['after']['g'] + 1, event['after']['r']
        assert (next_generator, next_relator) == (500, 17678)


# Explicit spelling records for the finite affine leaves. These are not an
# instruction interpreter. Columns are (state label, current tag, next tag,
# changed coordinate), copied by hand from the frozen table and affine stencils.
INCREMENT = (
    (1, 2, 1, 17), (2, 3, 4, 16), (5, 6, 7, 15), (7, 8, 5, 11),
    (15, 16, 11, 14), (16, 17, 21, 12), (19, 20, 1, 10), (20, 21, 18, 13),
    (24, 25, 23, 12), (25, 26, 27, 11), (27, 28, 27, 10), (29, 30, 10, 16),
    (30, 31, 1, 12),
)
POSITIVE = (
    (0, 1, 2, 2), (3, 4, 3, 6), (4, 5, 6, 7), (6, 7, 8, 8),
    (8, 9, 30, 7), (9, 10, 1, 5), (10, 11, 12, 6), (11, 12, 14, 6),
    (12, 13, 18, 3), (13, 14, 16, 6), (14, 15, 18, 4), (17, 18, 1, 5),
    (18, 19, 1, 1), (22, 23, 24, 1), (23, 24, 25, 1), (26, 27, 28, 3),
    (28, 29, 31, 3),
)
ZERO = (
    (0, 1, 3, 2), (3, 4, 5, 6), (4, 5, 4, 7), (6, 7, 9, 8),
    (8, 9, 1, 7), (9, 10, 11, 5), (10, 11, 13, 6), (11, 12, 15, 6),
    (12, 13, 19, 3), (13, 14, 17, 6), (14, 15, 20, 4), (17, 18, 22, 5),
    (18, 19, 18, 1), (22, 23, 26, 1), (23, 24, 29, 1), (26, 27, 23, 3),
)


def make_schedule():
    p = LiteralPresentation()
    p.initialize()
    p.affine('B0', (), (((1, 1),),), 'reset2={(0,n)}')
    p.affine('T', ((0, 1),), (((0, 1), (1, 1)),), 'tau S={(n+1,n)}')
    p.affine('Box1', (), (((0, 1),),), 'one-supported integer functions')
    p.binary('U0', 'B0', 'T', True, (12, 27, 6))
    p.omega('V0', 'U0', 2, 'B0 contains the zero 2-block', (33, 158, 19))
    p.shift_list('V0_shift_minus1', 'V0', -1)
    p.binary('W0', 'V0', 'V0_shift_minus1', False, (35, 196, 3))
    p.rho('N_rho1', 'W0', (57, 653, 6))
    p.pi('N_pi1', 'N_rho1', (69, 819, 65))
    p.rho('N_rho2', 'N_pi1', (91, 1644, 6))
    p.pi('N_pi2', 'N_rho2', (103, 1878, 99))
    p.binary('N', 'N_pi2', 'Box1', False, (105, 1979, 3))
    p.omega('G_N', 'N', 1, 'N contains zero and is one-supported', (123, 2079, 16))
    directions = tuple(((i, 1), (i + 9, 1)) for i in range(1, 9))
    edge_names = []
    for kind, records in (('I', INCREMENT), ('Dplus', POSITIVE), ('Dzero', ZERO)):
        for state, tag, next_tag, site in records:
            offset = ((0, tag), (9, next_tag))
            if kind != 'Dzero':
                offset = tuple(sorted(offset + ((site, 1),)))
            edge_directions = directions if kind != 'Dzero' else tuple(
                vector for i, vector in enumerate(directions, 1) if i != site)
            name = 'edge_' + kind + '_' + str(state)
            p.affine(name, offset, edge_directions, {'kind': kind, 'state': state,
                                                      'current_tag': tag, 'next_tag': next_tag,
                                                      'changed_or_omitted_coordinate': site})
            edge_names.append(name)
    p.affine('Clear', ((0, 22),), tuple(((i, 1),) for i in range(1, 9)), 'halt-tag to zero block')
    p.affine('Restart', (), tuple(((i, 1),) for i in range(9, 18)), 'zero source, arbitrary next block')
    edge_names.extend(('Clear', 'Restart'))
    assert len(edge_names) == 48 and sum(len(p.cache[name]) for name in edge_names) == 417
    current = edge_names[0]
    for index, right in enumerate(edge_names[1:], 1):
        name = 'Run_union_' + str(index) if index < 47 else 'R_bare'
        p.binary(name, current, right, True, (217, 2772, 6) if index == 47 else None)
        current = name
    p.omega('Omega', 'R_bare', 18, 'Restart contains the zero 18-block', (422, 6071, 203))
    p.shift_list('Omega_shift_minus9', 'Omega', -9)
    p.binary('H_bare', 'Omega', 'Omega_shift_minus9', False, (424, 6477, 3))
    p.binary('Hist_aff', 'H_bare', 'G_N', False, (426, 6496, 3))
    p.rho('Block_rho1', 'Hist_aff', (448, 10472, 6))
    p.pi('Block_pi1', 'Block_rho1', (460, 11420, 456))
    p.rho('Block_rho2', 'Block_pi1', (482, 16155, 6))
    p.shift_list('Block_shift_minus8', 'Block_rho2', -8)
    p.pi('Block_pi2', 'Block_shift_minus8', (494, 17171, 490))
    p.shift_list('Block_shift_plus8', 'Block_pi2', 8)
    p.affine('Box9', (), tuple(((i, 1),) for i in range(9)), 'arbitrary nine-block')
    p.affine('Init', ((0, 23),), (((1, 1),),), 'tag23, arbitrary input at site1')
    p.binary('Reach_aff', 'Block_shift_plus8', 'Box9', False, (496, 17671, 3))
    p.binary('Accepted', 'Reach_aff', 'Init', False, (498, 17676, 3))
    p.transducer()
    p.final_syntax_audit()
    return p, edge_names


def main():
    assert not OUTPUT.exists(), 'First output already exists; never replay this constructor.'
    dependencies = immutable_dependencies()
    presentation, edge_names = make_schedule()
    source_raw = Path(__file__).read_bytes()
    result = {
        'schema': 'positive7-preembedding-literal-presentation-v1',
        'scope': 'Literal syntax only; imported subgroup-identification premises remain attributed.',
        'excluded': ['group reduction or word-problem evaluation', 'machine execution',
                     'Mikaelian Section 7 embedding', 'matrix alphabet', 'Diophantine arithmetic bound'],
        'source': {'path_at_first_run': str(Path(__file__)), 'sha256': digest_bytes(source_raw),
                   'bytes': len(source_raw), 'LF_lines': source_raw.count(b'\n')},
        'dependencies': dependencies,
        'word_conventions': {
            'letters': 'nonzero signed sequential generator IDs',
            'empty_word': [], 'conjugation': 'inverse(by) + word + by',
            'relator': 'inverse(stable) + source + stable + inverse(target)',
            'simplification': 'none, including adjacent inverse letters',
            'input_renaming': 'old IDs retained as explicitly traced role aliases',
            'affine_basis': 'all nine tracked initial-A images retained literally after transport',
            'final_target': 'anchor uses current markers; direction uses tracked initial-A d/e'},
        'generators': presentation.generators,
        'relators': presentation.relators,
        'trace': presentation.events,
        'affine_edge_order': edge_names,
        'final_state': presentation.state(),
        'cached_lists': presentation.cache,
        'selected_list_name': 'X_U', 'selected_list': presentation.cache['X_U'],
        'census': {'generators': len(presentation.generators), 'relators': len(presentation.relators),
                   'selected_words': len(presentation.cache['X_U']),
                   'cached_lists': len(presentation.cache), 'events': len(presentation.events),
                   'relator_letters': sum(len(row['word']) for row in presentation.relators),
                   'cached_word_letters': sum(len(w) for words in presentation.cache.values() for w in words)},
        'status': 'first original literal-string emission; independent audit separate',
        'retained_boundaries': [
            'Every fresh omega letter remains distinct even when its displayed action duplicates another.',
            'The new wrapper output is excluded from persistent transport of old caches.',
            'The final two-relator stable letter does not normalize the marker F.',
            'The downstream Section 7.4 noninjective map blocks the historical conditional 20808 route; no such embedding is emitted.']}
    raw = (json.dumps(result, separators=(',', ':'), ensure_ascii=True) + '\n').encode()
    with OUTPUT.open('xb') as stream:
        stream.write(raw)
    print(json.dumps({'status': 'PASS', 'output': str(OUTPUT), 'sha256': digest_bytes(raw),
                      'bytes': len(raw), 'census': result['census']}))


if __name__ == '__main__':
    main()
