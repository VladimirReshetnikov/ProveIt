#!/usr/bin/env python3
"""Generate repeated-word candidates outside the union of sampled dictionaries.

The output is a pool of admissible binary productions, not a closed grammar.
Only words occurring at least twice in the longest semantic root are retained.
"""
import json
from pathlib import Path
from exact_exchange import load_context, HERE

names = ['baseline_fine_grammar.json', 'search_control.json',
         'search_baseline.json', 'search_reduced_locks.json', 'search_zero5.json']
old, roots, allowed, groups, expr, root, atoms, locks = load_context()
words = {w for name in names for w,l,r in json.loads((HERE/name).read_text())['rules']}
known = words | set(allowed)
source = max(roots, key=len)
productions = {}
for left in sorted(known):
    if left in allowed and not (allowed[left] & 1):
        continue
    for right in sorted(known):
        if right in allowed and not (allowed[right] & 2):
            continue
        word = left + right
        if word in known or len(word) > 120 or source.count(word) < 2:
            continue
        productions.setdefault(word, (left, right))
result = dict(rules=[[w, *productions[w]] for w in sorted(productions)],
              rules_count=len(productions),
              description=__doc__)
(HERE/'pool_repeated.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(dict(pool_words=len(words), new_words=len(productions),
                     maximum_word_length=max(map(len, productions)))))
