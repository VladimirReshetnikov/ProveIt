"""Check the exact node equation on genuine translated source fixtures.

This is an untrusted research utility. The universal equation is proved in
the report; finite counts do not prove the equivalence theorem.
"""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'newest_use'))
from translate import from_upstream, to_newest


def counts(proof):
    if not proof:
        return 0, 0
    tag = proof[0]
    children = []
    if tag in ('i', 'u'):
        children = [proof[-1]]
    elif tag == 'e':
        children = proof[-2:]
    elif tag != 'r':
        raise ValueError('unknown proof tag')
    parts = [counts(p) for p in children]
    return 1 + sum(n for n, u in parts), int(tag == 'u') + sum(u for n, u in parts)


def main():
    results = []
    for path in sorted((ROOT / 'newest_use/fixtures/source').glob('*.json')):
        goal, old = json.loads(path.read_text())
        source = from_upstream(old)
        target = to_newest(goal, source)
        n, u = counts(source)
        m, _ = counts(target)
        if m != n + 3 * u:
            raise ValueError((path.name, n, u, m))
        results.append({'fixture': path.name, 'source_nodes': n,
                        'source_uses': u, 'target_nodes': m,
                        'n_plus_3u': n + 3 * u})
    print(json.dumps({'exact_node_formula': 'n + 3u', 'fixtures': results}, indent=2))


if __name__ == '__main__':
    main()
