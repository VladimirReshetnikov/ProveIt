"""Independent finite binder audit of the K1 naming constructor.

This checks examples, not universal soundness. Pass a kernel source path.
"""
import importlib.util
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
spec = importlib.util.spec_from_file_location('audited_kernel', path)
kernel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernel)
counts = {'terms': 0, 'checks': 0}
for scope in range(4):
    leaves = list(range(-scope, 1))
    terms = leaves + [[0, value] for value in leaves]
    terms += [
        [counter, seed, body]
        for counter in leaves
        for seed in leaves
        for body in leaves + [1, [0, 1], [0, 0, 1], [0, 0, 2]]
        if kernel.valid([counter, seed, body], scope)
    ]
    for term in terms:
        if not kernel.valid(term, scope):
            raise ValueError('invalid audit term')
        formula = kernel.name(term)
        if not kernel.valid(formula, scope, formula=True):
            raise ValueError(('invalid naming formula', scope, term))
        fresh = -scope - 1
        body = kernel.opening(formula[0], fresh, 2)
        if not kernel.valid(body, scope + 1, depth=1, formula=True):
            raise ValueError('invalid opened body')
        if kernel.opening(body, 0) != [[0, term, fresh], term]:
            raise ValueError('incorrect zero row')
        if kernel.opening(body, [0, 0]) != [[[0, 0], term, fresh], term]:
            raise ValueError('incorrect one row')
        if kernel.derive(['n', term], [], scope) != formula:
            raise ValueError('incorrect naming rule')
        counts['terms'] += 1
        counts['checks'] += 6
print(json.dumps(counts, indent=2))
