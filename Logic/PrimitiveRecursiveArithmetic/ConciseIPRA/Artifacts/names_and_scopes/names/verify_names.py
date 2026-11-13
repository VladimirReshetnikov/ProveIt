"""Replay the K1 compiler and exercise the standalone checker.

This is finite implementation evidence, not a formalization of completeness.
The proof of completeness is the separate simultaneous rank induction.
"""
import ast
import io
import json
from pathlib import Path
import subprocess
import sys
import time
import tokenize

import names_kernel as N
import source_liberal as C
import compile_names as T

ROOT = Path(__file__).resolve().parent


def nodes(proof):
    tag, *args = proof
    if tag in ('c', 'n'):
        return 1
    if tag == 'u':
        return 1 + (nodes(args[-1]) if args[-1] is not None else 0)
    if tag in ('a', 'i'):
        return 1 + nodes(args[-1])
    return 1 + nodes(args[-1]) + nodes(args[-2])


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, separators=(',', ':')) + '\n')


def replay(data, expected=True):
    receipts = []
    for optimized in (False, True):
        command = [sys.executable, '-I', '-S']
        if optimized:
            command.append('-O')
        command.append(str(ROOT / 'names_kernel.py'))
        process = subprocess.run(command, input=json.dumps(data), text=True,
                                 capture_output=True, timeout=30)
        accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
        if accepted != expected:
            raise AssertionError((optimized, expected, process.stdout, process.stderr))
        receipts.append(dict(optimized=optimized, expected=expected, accepted=accepted))
    return receipts


def formula(value, depth, diagonal=False):
    result = [[[1, 1, value], [1, 1, 0]]] if diagonal else [[[1, 0, value], 0]]
    for _ in range(depth - 1):
        result = [result]
    return result


def main():
    started = time.monotonic()
    closed, opened, processes = [], [], []
    for file in sorted((ROOT / 'reference' / 'source_fixtures').glob('*.json')):
        source = json.loads(file.read_text())
        target = T.translate(source)
        write(ROOT / 'tests' / 'compiled' / file.name, target)
        processes.extend(dict(case=file.stem, **x) for x in replay(target))
        record = dict(case=file.stem, source_nodes=nodes(source['proof']),
                      target_nodes=nodes(target['proof']),
                      target_bytes=len(json.dumps(target, separators=(',', ':')).encode()))
        closed.append(record)
        print(json.dumps(record), flush=True)

    # Supplied arbitrary witnesses are recovered through Name(t).
    one = [0, 0]
    named = {'goal': N.name(one), 'proof': ['n', one]}
    source_name = {'goal': N.name(one),
                   'proof': ['i', N.name(one), one, ['c', [0, -1], one, one]]}
    compiled_name = T.translate(source_name)
    write(ROOT / 'tests' / 'name_one.json', named)
    write(ROOT / 'tests' / 'name_one_compiled.json', compiled_name)
    for label, data in [('name_one', named), ('name_one_compiled', compiled_name)]:
        processes.extend(dict(case=label, **x) for x in replay(data))

    # Full compound Alias is absent from the target, but compiled effectively.
    source_alias = {'goal': N.name(one),
                    'proof': ['a', one,
                              ['i', N.name(-1), -1,
                               ['c', [0, -2], -1, -1]]]}
    compiled_alias = T.translate(source_alias)
    write(ROOT / 'tests' / 'compound_alias_source.json', source_alias)
    write(ROOT / 'tests' / 'compound_alias_compiled.json', compiled_alias)
    processes.extend(dict(case='compound_alias_compiled', **x)
                     for x in replay(compiled_alias))

    # Newest Back, self-containing replacement, both introduction modes,
    # and nested D binders. These are open sequents, checked by derive().
    for self_occurring in (False, True):
        scope = 1 if self_occurring else 2
        source_parameter = -1
        replacement = [0, -1] if self_occurring else -2
        for depth in (1, 2, 3):
            for diagonal in (False, True):
                f = lambda value: formula(value, depth, diagonal)
                context = [([], [source_parameter, replacement]), ([], f(replacement))]
                use = lambda index: ['u', index, [0, [0, 0]], None]
                source = ['v', f(source_parameter), use(0), use(1)]
                goal = C.derive(source, context, scope)
                target = T.compile_proof(source, context, scope)
                if N.derive(target, context, scope) != goal:
                    raise AssertionError('open translation')
                label = f'open_self{int(self_occurring)}_depth{depth}_diag{int(diagonal)}'
                encoded = dict(scope=scope, context=context, goal=goal,
                               source_proof=source, target_proof=target)
                size = len(json.dumps(encoded, separators=(',', ':')).encode())
                # Avoid large redundant generated trees in the deliverable.
                saved = size <= 1000000
                if saved:
                    write(ROOT / 'tests' / 'open' / (label + '.json'), encoded)
                record = dict(case=label, target_nodes=nodes(target),
                              target_bytes=size, certificate_saved=saved)
                opened.append(record)
                print(json.dumps(record), flush=True)

    # Non-order-preserving embedding and noncontiguous clause placement.
    source_context = [([], [-1, -2]), ([], formula(-2, 2))]
    source = ['v', formula(-1, 2), ['u', 0, 0, None], ['u', 1, 0, None]]
    mapping = {-1: -3, -2: -1}
    mapped = [(T.rename(a, mapping), T.rename(b, mapping)) for a, b in source_context]
    receiving = [([], [0, 0]), mapped[0], ([], [[0, 0], [0, 0]]), mapped[1]]
    target = T.compile_proof(source, source_context, 2, receiving, 4, mapping,
                            [T.clause_realizer(1), T.clause_realizer(3)])
    if N.derive(target, receiving, 4) != formula(-3, 2):
        raise AssertionError('nonmonotone embedding')
    write(ROOT / 'tests' / 'open' / 'nonmonotone_embedding.json',
          dict(scope=4, context=receiving, goal=formula(-3, 2), target_proof=target))
    opened.append(dict(case='nonmonotone_embedding', target_nodes=nodes(target)))

    negatives = {
        'compound_alias_forbidden': {'goal': N.name(one),
                                     'proof': ['a', one, ['n', -1]]},
        'name_free_parameter': {'goal': N.name(one), 'proof': ['n', -1]},
        'name_boolean_leaf': {'goal': N.name(0), 'proof': ['n', False]},
        'name_unbound_index': {'goal': N.name(0), 'proof': ['n', 1]},
        'name_wrong_arity': {'goal': N.name(0), 'proof': ['n', []]},
        'name_extra_payload': {'goal': N.name(0), 'proof': ['n', 0, 0]},
        'false_goal': {'goal': [0, one], 'proof': ['n', one]},
        'name_wrong_goal': {'goal': N.name(0), 'proof': ['n', one]},
    }
    for label, data in negatives.items():
        write(ROOT / 'tests' / 'negative' / (label + '.json'), data)
        processes.extend(dict(case=label, **x) for x in replay(data, False))

    tree = ast.parse((ROOT / 'names_kernel.py').read_text())
    normalized = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    metrics = dict(significant_tokens=sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
                   ast_nodes=sum(1 for _ in ast.walk(tree)), normalized_bytes=len(normalized.encode()),
                   note='Complete module, including documentation strings; readable reference code, not a compact frontier candidate.')
    receipt = dict(closed_source_fixtures=len(closed), extra_closed_translations=2,
                   direct_naming_certificate=True, open_translations=len(opened),
                   standalone_subprocess_runs=len(processes), failures=0,
                   seconds=round(time.monotonic()-started, 3), python=sys.version,
                   kernel_metrics=metrics, closed=closed, open=opened, processes=processes,
                   limitation='Finite proof witnesses and malformed-input regressions; not a Lean/Rocq formalization or exhaustive verifier proof.')
    write(ROOT / 'evidence' / 'verification.json', receipt)
    print(json.dumps({k: v for k, v in receipt.items() if k not in ('closed', 'open', 'processes')}, indent=2))


if __name__ == '__main__':
    main()
