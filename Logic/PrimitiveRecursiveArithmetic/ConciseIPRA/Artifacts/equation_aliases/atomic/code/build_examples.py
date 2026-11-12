"""Build source proofs and compile the nontrivial rank-induction examples."""
from pathlib import Path
import json
import sys
import time
import compiler as C
import atomic_alias as K

ROOT = Path(__file__).resolve().parents[1]


def abstract(tree, symbol, index=1):
    if tree == symbol:
        return index
    if type(tree) is not list:
        return tree
    size = len(tree)
    return [abstract(child, symbol,
                     index + 2 * (size == 1) + (size == 3 and j == 2))
            for j, child in enumerate(tree)]


def box(term, depth):
    result = C.name(term).formula
    for _ in range(depth - 1):
        result = [result]
    return result


def box_proof(term, depth, length, scope):
    goal = box(term, depth)
    if depth == 1:
        return C.name(term).proof([None] * length, scope)
    return ['i', goal, 0, ['u', length, 0, None]]


def compound_specialization(depth):
    term = [0, [0, 0]]
    body = abstract(box('y', depth), 'y')
    closure = [body]
    major = ['i', closure, 0, box_proof([0, -1], depth, 1, 1)]
    base = box_proof(0, depth, 1, 1)
    goal = box(term, depth)
    return {'goal': goal, 'proof': ['e', goal, major, ['u', 0, term, base]]}


def main():
    records = []
    for depth in (1, 2):
        source = compound_specialization(depth)
        C.S.verify(source)
        start = time.monotonic()
        target = C.translate(source)
        label = 'compound_specialization_rank' + str(depth)
        for subdir, value in [('source_tests', source), ('tests', target)]:
            path = ROOT / subdir / (label + '.json')
            path.parent.mkdir(exist_ok=True)
            path.write_text(json.dumps(value, separators=(',', ':')) + '\n')
        records.append({'case': label, 'body_depth': depth,
                        'target_bytes': (ROOT/'tests'/(label+'.json')).stat().st_size,
                        'compile_seconds': round(time.monotonic()-start, 6)})
        print(records[-1], flush=True)
    (ROOT/'evidence'/'rank_examples.json').write_text(json.dumps(records, indent=2)+'\n')


if __name__ == '__main__':
    main()
