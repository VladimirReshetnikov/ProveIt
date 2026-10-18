#!/usr/bin/env python3
"""Independent, dependency-free checker for the proposed routing grammar.

This checks finite grammar, literal local traces, state accounting and the
searcher's AST invariants.  It does NOT certify complete TM simulation.
The SAT solver is not imported or executed.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
INPUTS = BASE / 'inputs'
TABLE = BASE / 'reference/context246/machine/zfc_prefix246_old.tm'


def audit(path, short_scan=False, allow_scanner_risk=False):
    data = json.loads(path.read_text())
    assert 'rules' in data and 'rules_count' in data, 'A concrete grammar is required.'
    source = json.loads((INPUTS / 'closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((INPUTS / 'semantic-symbols.json').read_text())
    encode = {name: char for char, name in symbols.items()}
    lines = (INPUTS / 'semantic.txt').read_text().splitlines()
    n, nr, na = map(int, lines[0].split())
    old, names = {}, {}
    for line in lines[1:n + 1]:
        split, word, state = line.split()
        split, state = int(split), int(state)
        assert word == ''.join(encode[t] for t in source['flattened_semantic_words'][str(state)])
        old[word] = (word[:split], word[split:])
        names[state] = word
    original_roots = lines[n + 1:n + nr + 1]
    allowed = {char: int(mask) for char, mask in map(str.split, lines[n + nr + 1:])}
    assert len(old) == n == 127 and len(original_roots) == nr == 24
    assert len(allowed) == na == len(symbols)
    assert set(original_roots) == {names[q] for q in source['required_entry_roots']}
    @lru_cache(None)
    def control_bounds(ast):
        row = source['ast_dag'][ast]
        if row[0] == 'L':
            op, *args = row[1]
            return (1 if op == 'dec' else args[0] if op == 'brk' else 0,
                    args[0] if op == 'cont' else 0)
        left_break, left_continue = control_bounds(row[1])
        right_break, right_continue = control_bounds(row[2])
        return max(left_break - 1, right_break, 0), max(left_continue, right_continue - 1, 0)
    for info in source['atoms'].values():
        assert control_bounds(info['ast']) == tuple(info['bounds']) == (0, 0)
    for ast in source['sequence_ast_roots'].values():
        row = source['ast_dag'][ast]
        assert row[0] == 'N' and control_bounds(row[1]) == control_bounds(row[2]) == (0, 0)
    @lru_cache(None)
    def fine_atoms(ast):
        row = source['ast_dag'][ast]
        if row[0] == 'N' and control_bounds(row[1]) == control_bounds(row[2]) == (0, 0):
            return fine_atoms(row[1]) + fine_atoms(row[2])
        return (ast,)
    fine_expansion = {char:fine_atoms(source['atoms'][name]['ast']) for char,name in symbols.items()}
    overrides = {int(q):word for q,word in data.get('root_word_overrides', {}).items()}
    if 'modified_AX_word' in data:
        assert data['original_AX_word'] == names[76]
        assert 76 not in overrides or overrides[76] == data['modified_AX_word']
        overrides[76] = data['modified_AX_word']
    override_checks = []
    for q,new_word in sorted(overrides.items()):
        assert q in source['required_entry_roots']
        # This initial extension changes externally entered roots. Internal
        # parents would require propagating the spelling change into their
        # expanded words, rather than just retargeting one external entry.
        assert all(p not in source['sequence_states'] for p,b in source['incoming'][str(q)])
        old_word = names[q]
        assert new_word and all(ch in symbols for ch in new_word)
        before = tuple(atom for ch in old_word for atom in fine_expansion[ch])
        after = tuple(atom for ch in new_word for atom in fine_expansion[ch])
        assert before == after, ('Override changes the exact sequence of closed AST atoms',q)
        override_checks.append(dict(state=q,original_symbols=len(old_word),new_symbols=len(new_word),
                                    exact_closed_AST_atoms=len(before),
                                    closed_atom_sequence_sha256=hashlib.sha256(json.dumps(before).encode()).hexdigest()))
        names[q] = new_word
        original_roots = [new_word if w == old_word else w for w in original_roots]
    assert len(set(names.values())) == len(names), 'Overlapping original-state word names need a separate allocation policy.'
    if data['status'] == 'sat':
        assert set(data['roots']) == set(original_roots)
    table = {}
    for line in TABLE.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, move, target = line.split()
        table[int(q), int(bit)] = (int(write), move, int(target))
    states = {q for q, bit in table}
    sequences = set(source['sequence_states'])
    assert len(states) == 246 and len(table) == 492
    assert {t for w, d, t in table.values()} - states == {254}
    for q in sequences:
        assert table[q, 0][:2] == (0, 'R') and table[q, 1][:2] == (1, 'R')
        assert [table[q, bit][2] for bit in (0, 1)] == source['rules'][str(q)]
    # The input's incoming list is checked against the literal table, not trusted.
    for q in sequences:
        actual = sorted([p, bit] for p, bit in table if table[p, bit][2] == q)
        assert actual == sorted(source['incoming'][str(q)])
    rules = {word: (left, right) for word, left, right in data['rules']}
    assert len(rules) == len(data['rules']) == data['rules_count']
    assert len(rules) <= data.get('bound',len(rules))
    if data['status'] != 'sat':
        assert all(word in rules for word in data['roots'])
    for word, children in rules.items():
        assert len(word) > 1 and word == ''.join(children)
        for bit, child in enumerate(children):
            assert child and (child in rules if len(child) > 1 else child in symbols)
            if len(child) == 1:
                assert allowed[child] & (1 << bit), (word, bit, child, 'terminal orientation')

    erase177 = data.get('erase177', False)
    requested_short_scan = bool(short_scan or data.get('short_scan', False))
    erased = ({177} if erase177 else set()) | ({74} if requested_short_scan else set())
    patches = {(58,0):(0,'L',84)} if requested_short_scan else {}
    if erase177:
        assert data['retarget'] == -2
        assert table[177, 0] == (0, 'R', 175) and table[177, 1] == (1, 'R', 207)
        assert {(q, b) for q, b in table if table[q, b][2] == 177} == {(153, 1), (159, 0)}
        assert table[153, 1] == (1, 'L', 177) and table[159, 0] == (0, 'L', 177)
    if requested_short_scan:
        assert table[58,0] == (0,'L',74)
        assert table[74,0] == (0,'L',84) and table[74,1] == (1,'L',4)
        assert {(q,b) for q,b in table if table[q,b][2] == 74} == {(58,0)}
    constraints = source['left_entry_projection_constraints']
    groups = defaultdict(list)
    fixed = []
    for constraint in constraints:
        reason = constraint['reason']
        direct = 'via' not in reason or (erase177 and reason['via'] == 177)
        rerouted = direct and (data['retarget'] == -2 or reason['source'] == data['retarget'])
        if rerouted:
            groups[reason['source'], reason['read']].append(constraint)
        else:
            fixed.append(constraint)
    routes = {(r['source'], r['read']): r['word'] for r in data.get('routes', [])}
    assert len(routes) == len(data.get('routes', [])), 'Duplicate routing group.'
    assert set(routes) == set(groups)
    assert all(word in rules for word in routes.values())
    assert all(source_state not in sequences | erased for source_state, bit in routes)
    released = []
    for q in source['required_entry_roots']:
        outside = [tuple(e) for e in source['incoming'][str(q)] if e[0] not in sequences]
        if outside and all(e in routes or e[0] in erased for e in outside):
            released.append(q)
    if 'released_entry_roots' in data:
        assert set(data['released_entry_roots']) == set(released)
    for q in source['required_entry_roots']:
        if q not in released:
            assert names[q] in rules
    assert names[96] in rules, 'The actual dispatcher root must be retained.'
    for q, bit in table:
        if q in sequences | erased or (q, bit) in routes or (q,bit) in patches:
            continue
        target = table[q, bit][2]
        assert target not in erased, 'An unchanged literal edge still enters an erased state.'
        if target in sequences:
            assert names[target] in rules, 'An unchanged edge enters an absent grammar root.'

    def project(word, bits):
        for bit in bits:
            assert word in rules, ('Projection entered an atom too early', word, bits)
            word = rules[word][int(bit)]
        return word

    boot_rows = data.get('boot_lock_rows', [])
    assert len({tuple(pair) for pair in boot_rows}) == len(boot_rows)
    for q,bit in boot_rows:
        assert q not in overrides, 'A changed root needs a new bootstrap contract.'
        assert names[q] in rules and project(names[q],str(bit)) == old[names[q]][bit]

    traces = []
    for (caller, read), group in sorted(groups.items()):
        assert {c['reason']['previous'] for c in group} == {0, 1}
        write, move, old_entry = table[caller, read]
        assert move == 'L'
        for c in group:
            reason = c['reason']
            assert write == reason['write']
            bits = c['prefix']
            if 'via' in reason:
                assert erase177 and reason['via'] == old_entry == 177
                bits = str(reason['previous']) + bits
            else:
                assert old_entry == c['root']
            # All routed paths inspect only the preceding bit and, if present,
            # the just-written bit, so no arbitrary surrounding tape is assumed.
            assert 1 <= len(bits) <= 2
            forced = str(reason['previous']) + str(write)
            assert bits == forced[:len(bits)]
            old_endpoint = old_entry
            for bit in bits:
                row = table[old_endpoint, int(bit)]
                assert row[:2] == (int(bit), 'R'), ('Nontransparent old routing state', old_endpoint)
                old_endpoint = row[2]
            target_word = ''.join(encode[t] for t in c['word'])
            if len(target_word) > 1:
                assert names[old_endpoint] == target_word
            else:
                assert source['atoms'][symbols[target_word]]['state'] == old_endpoint
            assert project(routes[caller, read], bits) == target_word
            traces.append(dict(source=caller, read=read, previous=reason['previous'],
                               prefix=bits, old_endpoint=old_endpoint,
                               target_word=target_word, steps=1 + len(bits),
                               final_head_offset=len(bits) - 1))
    for c in fixed:
        assert project(names[c['root']], c['prefix']) == ''.join(encode[t] for t in c['word'])

    by_ast = {int(ast): names[int(q)] for q, ast in source['sequence_ast_roots'].items()}
    assert len(by_ast) == len(source['sequence_ast_roots']), 'Ambiguous AST aliases.'
    visiting = set()

    def join(left, right):
        return 1 + left[0], max(1 + left[0], left[1], right[1]), 1 + max(left[2], right[2])

    @lru_cache(None)
    def ast_properties(ast):
        key = ('ast', ast)
        assert key not in visiting, ('Cyclic AST expansion', ast)
        visiting.add(key)
        if ast in by_ast:
            result = word_properties(by_ast[ast])
        else:
            row = source['ast_dag'][ast]
            result = (0, 0, 0) if row[0] == 'L' else join(ast_properties(row[1]), ast_properties(row[2]))
        visiting.remove(key)
        return result

    @lru_cache(None)
    def word_properties(word):
        key = ('word', word)
        assert key not in visiting, ('Cyclic word expansion', word)
        visiting.add(key)
        if len(word) == 1:
            result = ast_properties(source['atoms'][symbols[word]]['ast'])
        else:
            assert word in rules or word in old
            left, right = rules[word] if word in rules else old[word]
            result = join(word_properties(left), word_properties(right))
        visiting.remove(key)
        return result

    leading, zero_run, depth = ast_properties(source['original_ast'])
    if data['properties']:
        assert zero_run <= data.get('zero_bound',7) and depth <= 64
        if isinstance(data['properties'],list):
            assert data['properties'][:3] == [leading,zero_run,depth]
    if requested_short_scan and not allow_scanner_risk:
        assert zero_run <= 6, 'The shortened scanner requires the requested six-zero source bound before runtime checking.'
    if data.get('lead_constraint', -1) >= 0:
        assert leading == data['lead_constraint']
    entry_words = {names[q] for q in source['required_entry_roots'] if q not in released} | set(routes.values())
    reached = set()

    def visit(word):
        if len(word) == 1 or word in reached:
            return
        reached.add(word)
        for child in rules[word]:
            visit(child)

    for word in entry_words:
        visit(word)
    framework = len(states - sequences - erased)
    if 'framework_states' in data:
        # A CLI shortening may be applied to an otherwise unmodified grammar
        # certificate, whose stored framework count predates that patch.
        declared_framework = framework + int(requested_short_scan and not data.get('short_scan', False))
        assert declared_framework == data['framework_states']
    return dict(status='PASS', candidate=str(path.relative_to(BASE)),
                candidate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                baseline_table_sha256=hashlib.sha256(TABLE.read_bytes()).hexdigest(),
                grammar_states=len(rules), framework_states=framework,
                working_states=framework + len(rules),
                erased_framework_states=sorted(erased), released_entry_roots=released,
                short_scanner=requested_short_scan,
                six_zero_sufficient_condition=(zero_run<=6),
                scanner_risk_explicitly_permitted=bool(requested_short_scan and allow_scanner_risk),
                local_routing_cases=len(traces), fixed_projection_cases=len(fixed),
                statically_closed_semantic_atoms=len(symbols),
                root_word_override_checks=override_checks,
                boot_lock_rows_checked=len(boot_rows),
                route_traces=traces, unreachable_but_charged_rules=sorted(set(rules) - reached),
                search_AST_properties=dict(leading_zeros=leading, maximum_zero_run=zero_run, depth=depth),
                scope='Finite grammar and literal local routing audit only; complete TM simulation not established.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--short-scan',action='store_true')
    parser.add_argument('--allow-scanner-risk',action='store_true',help='Diagnostic only: actual runtime checks must decide a seven-zero candidate.')
    args = parser.parse_args()
    result = audit(args.candidate.resolve(), short_scan=args.short_scan,allow_scanner_risk=args.allow_scanner_risk)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
