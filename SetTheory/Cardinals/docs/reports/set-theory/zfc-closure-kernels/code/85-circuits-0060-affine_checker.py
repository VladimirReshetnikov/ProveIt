"""Full-file affine checking with an optional certified-known-zero box rule.

The literal affine executor and its original oracle are loaded unchanged from
Context246. The extension allows an additional zero decrement only before any
nonzero effect, and only on a register proved zero by the checked source product
invariant. See known_zero_oracle.tex for the compositional proof obligation.
"""
from contextlib import contextmanager
import json
from common import BASE, CERTIFICATE, EXCLUDED, PHYSICAL, L, inputs, guarded_sites, load_module
from admissible_guards import verify_transport

A = load_module('runtime_affine_reference', BASE / 'sources/prior/prefix_affine.py')
STRICT_ORACLE = A.oracle
BASE_TABLE = {(str(q), b): (w, 'R' if d == 1 else 'L', str(t))
              for (q, b), (w, d, t) in L.read_table(BASE / 'machine/zfc_prefix246_old.tm').items()}


def protected_rows():
    result = set()

    def visit(value):
        if isinstance(value, dict):
            if {'state', 'read', 'row'} <= set(value):
                result.add((str(value['state']), value['read']))
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    data = json.loads((BASE / 'results/macro-inductions.json').read_text())
    assert [t['name'] for t in data['block_theorems']] == [
        'seek73_block', 'carry95_block', 'return48_block', 'rollback112_block']
    assert [t['name'] for t in data['macro_theorems']] == [
        'positive_decrement', 'zero_decrement', 'increment']
    assert [t['name'] for t in data['mark_theorems']] == [f'mark_{r}' for r in range(9)]
    visit(data)
    assert len(result) == 42
    return result


PROTECTED = protected_rows()


def successor(pc, op, arg, zero):
    if op == 'CI' or op == 'CD' and not zero:
        return L.add_one(pc)
    if op == 'CD':
        return L.add_one(L.remove_to(pc, '0', 1))
    if op == 'CB':
        return L.add_one(L.remove_to(pc, '0', arg))
    if op == 'CC':
        return L.remove_to(pc, '1', arg)
    return None


class Tracking(dict):
    def __init__(self, table):
        super().__init__(table)
        self.used = set()

    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


class AffineChecker:
    def __init__(self, layout, domain='unrestricted'):
        assert domain in ('unrestricted', 'product')
        self.domain = domain
        sites, raw = inputs(layout)
        self.table = {(str(q), b): (w, 'R' if d == 1 else 'L', str(t))
                      for (q, b), (w, d, t) in raw.items()}
        self.require_macro_support(self.table)
        masks = None
        if domain == 'product':
            verify_transport((layout,))
            masks = json.loads(CERTIFICATE.read_text())['masks']
        self.cases = []
        for index, site, pc, op, arg, zero in guarded_sites(sites):
            if domain == 'product' and index in EXCLUDED:
                continue
            physical = PHYSICAL[arg] if op in ('CI', 'CD') else arg
            guard = (physical, zero) if op == 'CD' else None
            physical_masks = None
            if masks is not None:
                assert masks[site] is not None
                logical_masks = list(masks[site])
                if op == 'CD':
                    logical_masks[arg] &= 1 if zero else 6
                    assert logical_masks[arg] != 0
                physical_masks = [None] * 9
                for logical, target in enumerate(PHYSICAL):
                    physical_masks[target] = logical_masks[logical]
                assert all(mask in range(1, 8) for mask in physical_masks)
            nxt = successor(pc, op, arg, zero)
            extra = int(op == 'CD' and not zero)
            effect = ('inc', physical) if op == 'CI' else (
                ('dec', physical) if op == 'CD' and not zero else None)
            right = [('b', int(bit)) for bit in nxt or ''] + [
                ('r', 0, 1, 40 + extra + int(nxt is None) - len(nxt or '')),
                ('b', 1), ('box', ('plain', effect))]
            target = A.canon([('b', 1)], right)
            self.cases.append((index, pc, op, arg, zero, guard, target, physical_masks))
        assert len(self.cases) == (8391 if domain == 'unrestricted' else 8385)

    @staticmethod
    def require_macro_support(table):
        assert all(table.get(key) == BASE_TABLE[key] for key in PROTECTED), 'Changed macro-support row'

    @contextmanager
    def oracle(self, physical_masks):
        if physical_masks is None:
            yield
            return

        def extended(q, branch, state):
            answer = STRICT_ORACLE(q, branch, state)
            if answer is not None:
                return answer
            if q == '95' and len(state) == 2 and state[0] == 'mark':
                register = state[1]
                if 0 <= register < 9 and physical_masks[register] == 1:
                    return '112', ('plain', None), 0
            return None

        previous = A.oracle
        A.oracle = extended
        try:
            yield
        finally:
            A.oracle = previous

    def check(self, table, index, fuel=1500):
        self.require_macro_support(table)
        source_index, pc, op, arg, zero, guard, target, masks = self.cases[index]
        try:
            with self.oracle(masks):
                rules, steps = A.run(table, pc, guard, target, halt=op == 'CH', fuel=fuel)
            assert steps > 0
            return True, sum(rules.values()), None
        except AssertionError as error:
            return False, 0, 'fuel' if str(error) == 'symbolic fuel exhausted' else 'unsupported'
        except KeyError:
            return False, 0, 'missing'
