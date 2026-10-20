#!/usr/bin/env python3
"""Measure six code-dependent fourth parameters in two macro associations.

This is a bounded source/compiler experiment. It does not establish the
consistency strength, primitive runtime, or startup of any generated table.
"""
from pathlib import Path
import argparse
import hashlib
import importlib
import itertools
import json
import sys

import measure as m


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--k219', type=Path, required=True)
    ap.add_argument('--k221', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    m.require(__debug__ and not sys.flags.optimize, 'Assertions required')
    m.require(not a.out.exists(), 'Output must be fresh')
    library = a.k221 / 'portable'
    inputs = {}
    for root, names in [(library, ['source_language.py', 'build221.py']),
                        (a.k219, ['sites219.json', 'k219.native.tm'])]:
        for name in names:
            p = root / name
            h = m.sha(p.read_bytes())
            m.require(h == m.PINS[name], ('Input identity', p, h))
            inputs[name] = {'path': str(p.resolve()), 'sha256': h}
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(library.resolve()))
    s = importlib.import_module('source_language')
    b = importlib.import_module('build221')
    tree = s.tree(json.loads((a.k219 / 'sites219.json').read_text()))
    table = b.read_table((a.k219 / 'k219.native.tm').read_bytes())
    groups, _ = b.decoder_map(table, tree)
    q = lambda k: b.sole(groups, k)
    macros = {'A': q(98), 'B': q(12), 'C': q(166)}
    relation = (q(90), ('CI', 1))
    # Source 140 orientation_postfix.py identifies precisely this existing
    # fourth-parameter read. Bind its complete primitive spelling as well.
    old_word = m.flat(tree)
    read_word = old_word[161:194]
    m.require(len(read_word) == 33, 'Read interval')
    m.require(read_word[:19] == m.flat(q(98)[0]), 'Read starts with old PUSH')
    m.require(set(i for op, i in read_word if op in ('CI', 'CD')) == {1, 2, 6, 7, 8},
              'Read touches only top, stack, scratch, input')
    identity, baseline = m.compile_tree(s, b, table, tree, tree)
    m.require(identity == table and baseline['working_states'] == 219, 'Baseline control')
    pair = lambda x, y: (x+y)*(x+y+1)//2+y
    a.out.mkdir(parents=True)
    results = []
    for x, y in itertools.permutations('ABC', 2):
        for association in ('left', 'right'):
            left, right = macros[x], macros[y]
            replacement = ((left, right), relation) if association == 'left' else (left, (right, relation))
            m.require(s.boundary(replacement) == (0, 0, False), 'Replacement closed')
            source = m.splice(s, tree, 161, 194, replacement)
            rows = s.sites(source)
            m.require(m.flat(source) == old_word[:161] + m.flat(replacement) + old_word[194:],
                      'Only the fourth-field read changes')
            m.require(s.graph_arithmetic(rows)[0] == s.graph_intervals(rows), 'Independent full CFG')
            tests = 0
            max_steps = 0
            for av, bv, cv, tail in itertools.product(range(3), repeat=4):
                registers = [11, cv, 17, cv, av, bv, 0, 0, tail]
                values = {'A': av, 'B': bv, 'C': cv}
                got, steps = m.run_macro(s, replacement, registers)
                want = registers.copy()
                want[1] = 4*pair(values[x], values[y])+1
                want[2] = pair(cv, 17)
                m.require(got == want, ('R replacement', x, y, registers, got, want))
                tests += 1
                max_steps = max(max_steps, steps)
            name = f'R{x}{y}-{association}'
            out = a.out / name
            out.mkdir()
            (out / 'sites.json').write_bytes(s.compact(rows))
            result = {'name': name, 'fourth_parameter': f'R(code{x},code{y})',
                      'association': association, 'source_metrics': s.metrics(source),
                      'source_sha256': m.sha(s.compact(rows)),
                      'replacement_primitives': len(m.flat(replacement)),
                      'removed_read_primitives': 33, 'proof_fields_removed': 1,
                      'finite_macro_checks': tests, 'maximum_test_steps': max_steps,
                      'unchanged': 'All other primitive occurrences, including rho5, final V/K bundle and its c!=a,b gate.',
                      'input_contract': 'This replacement leaves register8 unchanged; the alternative proof encoding omits the old fourth field.'}
            try:
                tt, compiled = m.compile_tree(s, b, table, tree, source)
                result['compiler'] = compiled
                raw = b.table_bytes(tt)
                (out / 'raw-candidate.tm').write_bytes(raw)
                result['table_sha256'] = m.sha(raw)
            except (ValueError, KeyError, AssertionError) as e:
                result['compiler_error'] = repr(e)
            m.dump(out / 'result.json', result)
            results.append(result)
    m.require(all(m.sha(Path(d['path']).read_bytes()) == d['sha256'] for d in inputs.values()), 'Input changed')
    result = {'status': 'SIX_MEMBERSHIP_BUILDERS_MEASURED', 'inputs': inputs,
              'baseline_metrics': s.metrics(tree), 'baseline_compiler_control': baseline,
              'variants': results, 'total_finite_macro_checks': sum(v['finite_macro_checks'] for v in results),
              'association_scope': 'Exactly the two binary associations of the three closed macro atoms PUSH_COPY(x), PUSH_COPY(y), RELATION. No search over internal primitive associations.',
              'limits': ['No consistency calibration of any restricted calculus.',
                         'No primitive runtime, bootstrap, or exact-machine theorem for generated tables.',
                         'Raw compiler counts, if available, retain the original initialization; they are not validated candidate state bounds.']}
    m.dump(a.out / 'result.json', result)
    print(json.dumps({k: result[k] for k in ['status', 'total_finite_macro_checks', 'association_scope']}, indent=2))
    for r in results:
        print(json.dumps({k: v for k, v in r.items() if k in ['name', 'source_metrics', 'compiler', 'compiler_error']}, sort_keys=True))


if __name__ == '__main__':
    main()
