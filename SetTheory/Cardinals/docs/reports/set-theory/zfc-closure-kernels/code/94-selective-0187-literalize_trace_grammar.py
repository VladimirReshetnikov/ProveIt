#!/usr/bin/env python3
"""Recover a literal-word grammar from the frozen read/write trace incumbent.

This is a positive result at 245 states, not a state-count reduction.  The
independent trace checker runs first.  We then require every retained old
word to expand to exactly its old spelling.  The binary compiler separately
checks register-program bisimulation; matching ordered leaves alone would
not suffice for the control-flow proof.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

from check_trace_grammar import check
from trace_commutation import TraceNormalizer


def literalize(reference, candidate, output):
    check(reference, candidate)
    source = json.loads((reference / 'inputs/closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((reference / 'inputs/semantic-symbols.json').read_text())
    nf = TraceNormalizer(source, symbols).normalize
    data = json.loads(candidate.read_text())
    rules = {w: (a, b) for w, a, b in data['rules']}

    @lru_cache(None)
    def spell(word):
        return word if len(word) == 1 else spell(rules[word][0]) + spell(rules[word][1])

    rows = (reference / 'inputs/state_reduction/route-grammar.txt').read_text().splitlines()
    n = int(rows[0].split()[0])
    checked = 0
    for row in rows[1:n + 1]:
        _, word, _ = row.split()
        if nf(word) in rules:
            assert spell(nf(word)) == word, ('A retained literal word changed', word)
            checked += 1
    literal = [[spell(w), spell(a), spell(b)] for w, (a, b) in rules.items()]
    assert len({w for w, _, _ in literal}) == len(rules)
    assert all(w == a + b for w, a, b in literal)
    data.update(
        status='LITERAL_ROUTING_GRAMMAR', rules=literal,
        roots=[spell(w) for w in data['roots']],
        routes=[dict(r, word=spell(r['word'])) for r in data['routes']],
        short_scan=True, framework_states=117,
        trace_search_origin='best_readwrite.json: same literal source, reordered factorization; 128 grammar states, depth 47')
    data.pop('boot_lock_rows', None)
    output.write_text(json.dumps(data, indent=2) + '\n')
    return {'status': 'PASS_LITERAL_WORD_RECOVERY', 'rules': len(rules),
            'retained_original_words_checked': checked,
            'scope': 'Literal grammar recovery; binary compilation is a separate check.'}


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference', type=Path, required=True)
    ap.add_argument('--candidate', type=Path, default=Path(__file__).with_name('best_readwrite.json'))
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        ap.error('Assertions are required; do not use -O.')
    print(json.dumps(literalize(args.reference, args.candidate, args.output), indent=2))
