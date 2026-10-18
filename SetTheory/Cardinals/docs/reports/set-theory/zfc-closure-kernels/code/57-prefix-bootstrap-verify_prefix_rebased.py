#!/usr/bin/env python3
"""Rebuild and audit the prefix-right-decrement 252-state research table.

The finite startup is literal and exact on the whole tape. The 8,366 affine
cases use three original Box excursions and the new positive-decrement lemma
in logic_audit/prefix_decrement_proof.md. This is not a proof-assistant build.
"""
from pathlib import Path
from collections import Counter
from types import SimpleNamespace
import hashlib, json, sys, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / 'redesign'))
import mp_protocol_runtime as m
sys.path.insert(0, str(ROOT / 'logic_audit'))
from prefix_phase import assert_prefix_phase

PERM = (7, 8, 4, 2, 5, 6, 0, 3, 1)
ENGINE = {
    (75, 1): (1, 'L', 85),
    (85, 0): (0, 'L', 85), (85, 1): (1, 'L', 97),
    (97, 0): (0, 'L', 112), (97, 1): (1, 'L', 97),
    (112, 0): (0, 'R', 131), (112, 1): (1, 'L', 97),
    (131, 0): (0, 'R', 95),
}

def construct():
    table, nodes = m.generate()
    inverse = {v: i for i, v in enumerate(m.audit.PERM)}
    for q, b in m.audit.SELECTOR_INCOMING:
        key = str(q), b
        w, d, t = table[key]
        original_physical = inverse[m.a.SKIP.index(int(t))]
        table[key] = w, d, str(m.a.SKIP[PERM[original_physical]])
    for (q, b), (w, d, t) in ENGINE.items():
        table[str(q), b] = w, d, str(t)
    return table, nodes

def prefix_checker():
    path = ROOT / 'source/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    raw = path.read_text().split('\ndef audit(', 1)[0]
    raw = raw.replace('40-len(pc)', '43-len(pc)')
    old = """        if answer is not None:
            q,newstate=answer;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue"""
    new = """        if answer is not None:
            if q=='43' and branch is not None and not branch[1] and seg[1][0]=='mark':
                prefix_phase_records.append(assert_prefix_phase(left))
                left=[('b',1)]+left
            q,newstate=answer;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue"""
    assert raw.count(old) == 1
    raw = raw.replace(old, new)
    # Only the run/canon definitions are used. In this variant the positive
    # decrement contract is new; the upstream unused audit/CLI is excluded.
    sys.modules['cost_search'] = SimpleNamespace()
    ns = {'__name__': 'prefix_runtime_checker', 'assert_prefix_phase': assert_prefix_phase,
          'prefix_phase_records': []}
    exec(compile(raw, str(path), 'exec'), ns)
    return ns

def certify(table, nodes):
    ns = prefix_checker()
    totals = Counter()
    ncases = 0
    minimum_literal = 10**9
    no_stray = overflow_cases = 0
    def decode(pointer):
        node, consumed = 0, ''
        for _ in range(len(nodes) + 1):
            bit = pointer[len(consumed)] if len(consumed) < len(pointer) else '0'
            consumed += bit
            op, *args = nodes[node][int(bit)].split()
            if op == 'CN':
                node = int(args[0])
            else:
                assert not any(b == '1' for b in pointer[len(consumed):]), ('stray successor bit', pointer, consumed)
                return consumed, op
        raise AssertionError('Source decoder does not terminate')
    for p, op, oldphysical in m.a.sites:
        for zero in ((True, False) if op == 'CD' else (None,)):
            r = PERM[oldphysical] if op in ('CI', 'CD') else oldphysical
            branch = (r, zero) if op == 'CD' else None
            nxt = m.audit.successor(p, op, r, zero)
            if op != 'CH':
                decode(nxt or '')
                no_stray += 1
                overflow_cases += nxt is None
            effect = ('inc', r) if op == 'CI' else ('dec', r) if op == 'CD' and not zero else None
            growth = int(op == 'CD' and not zero)
            right = [] if nxt is None else [('b', int(b)) for b in nxt]
            right += [('r', 0, 1, 43 + growth + (nxt is None) - len(nxt or '')),
                      ('b', 1), ('box', ('plain', effect))]
            rules, literal = ns['run'](table, p, branch, ns['canon']([('b', 1)], right),
                                       halt=op == 'CH', fuel=1000)
            assert literal > 0
            minimum_literal = min(minimum_literal, literal)
            totals.update(rules)
            ncases += 1
    assert len(m.a.sites) == 6441 and ncases == 8366 and no_stray == 8365
    phases = ns['prefix_phase_records']
    assert len(phases) == 1925
    return dict(passed=True, cases_passed=ncases, source_leaf_sites=len(m.a.sites),
                minimum_literal_steps=minimum_literal, rule_totals=dict(totals),
                positive_phase_premises_checked=len(phases),
                nonhalting_successors_no_stray_checked=no_stray, overflow_cases=overflow_cases,
                quantification='All gap >= 43 and all nine natural-valued registers; each CD branch has its named zero/nonzero guard.',
                contracts='Three published Box excursions plus the new prefix-right positive-decrement lemma. No fresh kernel build.')

def literal_startup(table):
    q, h, ones = '64', 0, set()
    used = Counter()
    checkpoints = []
    for step in range(25613):
        if step in (0, 9, 1000, 10000, 25612):
            checkpoints.append(dict(step=step, state=int(q), head=h, ones=sorted(ones)))
        if step == 25612:
            break
        assert q != '254', ('unexpected halt', step)
        key = q, int(h in ones)
        used[key] += 1
        w, d, q = table[key]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += 1 if d == 'R' else -1
    expected = {3, 47, 49, 51, 53, 55, 57, 59, 61, 63, 65}
    assert q == '96' and h == 4 and ones == expected
    assert ones == m.audit.paint('', 43, [0] * 9, [], 4)
    return dict(passed=True, literal_steps=25612, final_state=96, final_head=4,
                whole_one_positions=sorted(ones), all_other_cells_zero=True,
                pc='', gap=43, physical_registers=[0] * 9, logical_registers=[0] * 9,
                spare_blocks=[], used_rows=len(used), used_states=len({q for q, _ in used}),
                checkpoints=checkpoints)

def canonicalize(table):
    states = {int(q) for q, _ in table}
    ordered = [64] + sorted(states - {64})
    mapping = {q: i for i, q in enumerate(ordered)}
    mapping[254] = len(states)
    canonical = {(mapping[int(q)], b): (w, d, mapping[int(t)])
                 for (q, b), (w, d, t) in table.items()}
    raw = '#! start 0\n' + ''.join(f'{q} {b} {w} {d} {t}\n'
                                 for (q, b), (w, d, t) in sorted(canonical.items()))
    assert len(states) == 252 and set(canonical) == {(q, b) for q in range(252) for b in (0, 1)}
    assert all(t in range(253) for _, _, t in canonical.values())
    return raw.encode(), mapping

def main():
    assert __debug__, 'Run with Python assertions enabled.'
    started = time.monotonic()
    table, nodes = construct()
    assert len(table) == 504
    affine = certify(table, nodes)
    startup = literal_startup(table)
    data = m.a.encoded(table)
    canonical, mapping = canonicalize(table)
    oldpath = HERE / 'prefix_rebased252.tm'
    newpath = HERE / 'prefix_rebased252_canonical.tm'
    oldpath.write_bytes(data)
    newpath.write_bytes(canonical)
    (HERE / 'prefix_renumbering.json').write_text(json.dumps(mapping, indent=2) + '\n')
    result = dict(status='ordinary_checks_pass', working_states=252, binary_symbols=2,
                  blank_symbol=0, old_start=64, old_halt=254, canonical_start=0, canonical_halt=252,
                  sha256_old=hashlib.sha256(data).hexdigest(),
                  sha256_canonical=hashlib.sha256(canonical).hexdigest(),
                  physical_permutation=list(PERM),
                  logical_to_physical=[PERM[p] for p in m.audit.PHYS],
                  affine=affine, startup=startup,
                  state_graph=m.audit.graph_audit({(int(q), b): (w, d, int(t)) for (q, b), (w, d, t) in table.items()}),
                  elapsed_seconds=time.monotonic() - started,
                  scope='A new 252-state engine and startup. No verified table below 252 states and no fresh Lean/Coq build are claimed.')
    (HERE / 'prefix_rebased_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'startup'}, indent=2))
    print('Exact blank startup: 25,612 steps; q96, head4, gap43, nine zero registers, no spare blocks.')

if __name__ == '__main__':
    main()
