"""Fresh static review only. No SLP values or degree propagation; no imports of author code."""
import hashlib
import json
from collections import Counter
from pathlib import Path

B = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
def ck(test, label):
    if not test:
        raise ValueError(label)
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def refs(row):
    return [x for x in row[2:] if type(x) is str]
def structural(form):
    free = set(form['parameters'] + form['auxiliaries'])
    known = set(free)
    defs = {}
    roles = set()
    for row in form['source']:
        name, op, left, right = row
        ck(name not in known and op in ['*', '+', '-'], 'producer')
        for arg in [left, right]:
            if type(arg) is str:
                ck(arg in known, 'topology')
            elif type(arg) is int:
                pass
            else:
                ck(type(arg) is dict and set(arg) == {'fixed_numeral'}, 'numeral')
                roles.add(arg['fixed_numeral'])
        known.add(name)
        defs[name] = row
    live = set()
    stack = [form['output']]
    while stack:
        name = stack.pop()
        if name in live:
            continue
        live.add(name)
        if name in defs:
            stack.extend(refs(defs[name]))
    ck(live == known, 'liveness')
    ck(roles == set(form['fixed_numeral_recipes']), 'fixed roles')
    count = Counter(row[1] for row in form['source'])
    return {'M': count['*'], 'A': count['+'] + count['-'], 'total': len(defs),
            'free_ports': len(free), 'witnesses': len(form['auxiliaries']), 'fixed_roles': len(roles)}

raw_parent = (B / 'neary_woods_hierarchical_history250_tesla.json').read_bytes()
raw_child = Path('/tmp/neary_woods_scaled_strong249_tesla.json').read_bytes()
ck(sha(raw_parent) == 'd2f1ae7870cb8ec295d4401a8e9c951047f0e92cf2b6e6f4bb723c6b483f1ebf', 'parent pin')
ck(sha(raw_child) == 'e8fb322a18ec77cf9936ebb7d9e25d86414b66f8db561c4a64edb2ef16aba35c', 'child pin')
parents = json.loads(raw_parent)['forms']
children = json.loads(raw_child)['forms']
ck(len(parents) == 2 and len(children) == 6, 'form counts')
results = []
for pi, parent in enumerate(parents):
    immutability = json.dumps(parent, sort_keys=True)
    parent_meta = structural(parent)
    ck((parent_meta['M'], parent_meta['A'], parent_meta['total']) == (130, 120, 250), 'parent ledger')
    old = {r[0]: r for r in parent['source']}
    factors = set(parent['unit_factors'])
    ck(len(factors) == 16, 'factor count')
    pending = ['lower_history_product']
    leaves = []
    spine = []
    while pending:
        name = pending.pop()
        if name in factors:
            leaves.append(name)
        else:
            row = old[name]
            ck(row[1] == '*' and len(refs(row)) == 2, 'product spine')
            spine.append(row)
            pending.extend(refs(row))
    ck(Counter(leaves) == Counter(parent['unit_factors']) and len(spine) == 15, 'factor occurrences')
    for cores, degree in [(['geo__'], 936), (['and__'], 1038), (['geo__', 'and__'], 1048)]:
        child = children[len(results)]
        expected = {n: r[:] for n, r in old.items()}
        deleted = []
        edits = []
        added = []
        consumers = []
        guards = []
        for pre in cores:
            block = [
                [pre+'c2', '*', pre+'R10a', pre+'R10a'],
                [pre+'Ac2', '*', pre+'A', pre+'c2'],
                [pre+'L16', '*', pre+'f', pre+'f'],
                [pre+'ic2', '*', pre+'i', pre+'c2'],
                [pre+'ic22', '*', pre+'ic2', pre+'ic2'],
                [pre+'normalized_strong_Q', '*', pre+'A', pre+'ic22'],
                [pre+'f_square_minus_one', '-', pre+'L16', pre+'normalized_strong_Q'],
                [pre+'R16', '*', pre+'A', pre+'normalized_strong_Q']]
            for row in block:
                ck(old[row[0]] == row, 'paid literal')
            guards.extend(block)
            for suffix, targets in [('ic2', ['ic22']), ('ic22', ['normalized_strong_Q']), ('normalized_strong_Q', ['f_square_minus_one', 'R16'])]:
                name = pre + suffix
                actual = sorted(r[0] for r in parent['source'] if name in refs(r))
                ck(actual == sorted(pre+t for t in targets), 'private consumers')
                consumers.append({'name': name, 'consumers': actual})
            for suffix in ['ic2', 'ic22', 'normalized_strong_Q']:
                deleted.append(expected.pop(pre+suffix))
            for row in [[pre+'R16', '*', pre+'scaled_aux_root', pre+'scaled_aux_root'],
                        [pre+'f_square_minus_one', '-', pre+'scaled_f_square', pre+'R16']]:
                edits.append({'old': old[row[0]], 'new': row})
                expected[row[0]] = row
            for row in [[pre+'scaled_aux_root', '*', pre+'i', pre+'Ac2'],
                        [pre+'scaled_f_square', '*', pre+'A', pre+'L16']]:
                added.append(row)
                expected[row[0]] = row
        multiplier = cores[0]+'A' if len(cores) == 1 else 'scaled_discriminant_product'
        if len(cores) == 2:
            row = [multiplier, '*', 'geo__A', 'and__A']
            expected[multiplier] = row
            added.append(row)
        output = parent['output']
        ck(old[output] == [output, '-', 'lower_history_product', 1], 'old output')
        row = [output, '-', 'lower_history_product', multiplier]
        expected[output] = row
        edits.append({'old': old[output], 'new': row})
        actual = {r[0]: r for r in child['source']}
        ck(actual == expected, 'all complete row definitions')
        for key in ['parameters', 'auxiliaries', 'domains', 'fixed_numeral_recipes', 'fixed_u9_recipe', 'merged', 'output']:
            ck(child[key] == parent[key], 'interface ' + key)
        ck(child['parent_factors_historical'] == parent['unit_factors'], 'historical factor list')
        ck(child['cores_scaled'] == cores and child['multiplier_port'] == multiplier, 'variant')
        ck(child['comparisons'] == [['lower_history_product', multiplier]], 'comparison')
        ledger = structural(child)
        ck((ledger['M'], ledger['A'], ledger['total'], ledger['witnesses']) == (129, 120, 249, 43), 'child ledger')
        retained = sum(old.get(n) == r for n, r in actual.items())
        ck(retained == (244 if len(cores) == 1 else 239), 'literal retained count')
        ck(child['certificate'] == {'operations': 248, 'M': 129, 'A': 119, 'comparisons': 1, 'witnesses': 43}, 'certificate')
        results.append({'interface_index': pi, 'merged': parent['merged'], 'cores': cores,
                        'ledger': ledger, 'literal_retained_rows': retained,
                        'removed': deleted, 'edited': edits, 'added': added,
                        'private_consumer_guards': consumers, 'literal_paid_rows': guards,
                        'factor_spine': spine, 'factor_occurrences': dict(Counter(leaves)),
                        'source_sha256': sha(json.dumps(child['source'], sort_keys=True, separators=(',', ':')).encode()),
                        'manual_corrected_degree_bound': degree,
                        'old_saved_degree_bound': child['manual_degree_upper_bound']})
    ck(json.dumps(parent, sort_keys=True) == immutability, 'parent immutable')

first = {r[0]: r for r in parents[0]['source']}
second = {r[0]: r for r in parents[1]['source']}
ck([n for n in first if first[n] != second[n]] == ['program_duration_bound'], 'two-interface sole row difference')
receipt = {'parent_json_sha256': sha(raw_parent), 'old_author_json_sha256': sha(raw_child),
           'fresh_checker_sha256': sha(Path(__file__).read_bytes()), 'forms': results,
           'total_rows_checked': sum(r['ledger']['total'] for r in results),
           'source_array_values_evaluated': False, 'source_degree_propagation_executed': False,
           'saved_or_predecessor_code_executed_or_imported': False,
           'scope': 'Static source graphs and exact prescribed edits only. Degree and positivity proof are handwritten.'}
Path('/tmp/scaled249_static_read_aristotle.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS:1494 rows, six249=129M120A sources,43w,11 fixed numeral roles; no source evaluations.')
