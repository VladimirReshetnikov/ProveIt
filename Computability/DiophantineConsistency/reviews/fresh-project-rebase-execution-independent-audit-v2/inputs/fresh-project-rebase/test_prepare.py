#!/usr/bin/env python3
"""Toy checks for conservative ancestry selection and sibling artifact isolation."""
import hashlib
from pathlib import Path
import tempfile
import unittest
import prepare

def graph(changed=False):
    order = ['P.A', 'P.B', 'P.C', 'P.D']
    deps = {'P.A': [], 'P.B': ['P.A'], 'P.C': [], 'P.D': ['P.B', 'P.C']}
    rows = {n: {'sha256': ('new' if changed and n == 'P.A' else n),
                'imports': deps[n], 'workspace_path': n+'.lean'} for n in order}
    return {'order': order, 'sources': rows, 'project_modules': len(order), 'target': order[-1]}

def records(m):
    return [{'module': n, 'direct_inputs': {d: {'kind': 'project'} for d in m['sources'][n]['imports']}}
            for n in m['order']]

class PrepareTests(unittest.TestCase):
    def test_reverse_closure_and_transitive_ancestors(self):
        old, new = graph(), graph(True)
        plan = prepare.select(old, new, records(old))
        self.assertEqual(plan['changed'], ['P.A'])
        self.assertEqual(plan['affected'], ['P.A', 'P.B', 'P.D'])
        self.assertEqual(plan['unaffected'], ['P.C'])
        self.assertEqual(plan['project_ancestor_counts']['P.D'], 3)

    def test_rejects_hidden_actual_dependency(self):
        old = graph(); rs = records(old)
        rs[2]['direct_inputs']['P.A'] = {'kind': 'project'}
        with self.assertRaises(ValueError): prepare.select(old, graph(True), rs)

    def test_rejects_project_dependency_disguised_as_package(self):
        old = graph(); rs = records(old)
        rs[1]['direct_inputs']['P.A']['kind'] = 'package'
        with self.assertRaises(ValueError): prepare.select(old, graph(True), rs)

    def test_rejects_non_topological_graph(self):
        old = graph(); new = graph(True)
        new['sources']['P.A']['imports'] = ['P.D']
        with self.assertRaises(ValueError): prepare.select(old, new, records(old))

    def test_parent_observation_must_bind_actual_terminal_success(self):
        pair = Path('/tmp/pair-state.json')
        valid = {'observed_exit_code': 0, 'observed_stdout': 'author exit 0\nMATCHED_PASS 4 rows\n',
                 'pair_state_sha256': 'digest', 'pair_state_path': str(pair)}
        prepare.check_parent_observation(valid, 'digest', pair, 4)
        for change in ({'observed_exit_code': None}, {'observed_exit_code': 1},
                       {'observed_stdout': 'MATCHED_PASS 3 rows\n'},
                       {'pair_state_sha256': 'wrong'}, {'pair_state_path': '/tmp/other'}):
            with self.assertRaises(ValueError):
                prepare.check_parent_observation(dict(valid, **change), 'digest', pair, 4)

    def test_copies_each_sibling_without_links_and_checks_companions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); parents = {}; outputs = {}
            for label, value in (('author', b'alpha'), ('peer', b'beta')):
                lib = root/label/'lib'; stem = lib/'P/C'; stem.parent.mkdir(parents=True)
                obj = Path(str(stem)+'.olean'); obj.write_bytes(value)
                records_for_file = {}
                for suffix in prepare.SUFFIXES:
                    p = Path(str(stem)+suffix)
                    records_for_file[str(p)] = ({'realpath': str(p.resolve()),
                                                 'sha256': hashlib.sha256(value).hexdigest()}
                                                if suffix == '.olean' else None)
                parents[label] = lib; outputs[label] = {'P.C': records_for_file}
            new_a, new_b = root/'new-author', root/'new-peer'
            seed_a = prepare.copy_seeds(parents['author'], new_a, ['P.C'], outputs['author'])
            seed_b = prepare.copy_seeds(parents['peer'], new_b, ['P.C'], outputs['peer'])
            prepare.verify_seeds(new_a, seed_a); prepare.verify_seeds(new_b, seed_b)
            a, b = new_a/'P/C.olean', new_b/'P/C.olean'
            self.assertEqual(a.read_bytes(), b'alpha'); self.assertEqual(b.read_bytes(), b'beta')
            self.assertNotEqual(a.stat().st_ino, (parents['author']/'P/C.olean').stat().st_ino)
            a.write_bytes(b'changed')
            with self.assertRaises(ValueError): prepare.verify_seeds(new_a, seed_a)
            self.assertEqual(b.read_bytes(), b'beta')
            self.assertEqual((parents['author']/'P/C.olean').read_bytes(), b'alpha')
            (parents['author']/'P/C.ir').write_bytes(b'unexpected')
            with self.assertRaises(ValueError):
                prepare.copy_seeds(parents['author'], root/'bad', ['P.C'], outputs['author'])

if __name__ == '__main__': unittest.main()
