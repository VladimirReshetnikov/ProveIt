"""Untrusted compiler of conditional_copy proof trees to two-field streams."""
import copy
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('control', ROOT / 'reference/conditional_copy.py')
control = importlib.util.module_from_spec(spec)
spec.loader.exec_module(control)


def convert(data):
    goal, proof = data
    control.check(copy.deepcopy(data))

    def emit(p, g):
        n = len(g)
        b = -n
        code, *args = p
        if type(code) is int:
            t, q = args
            base, B = g[code]
            instructions = [[code, t]]
            if base:
                instructions.extend(emit(q, g))
            return instructions
        if code:
            r, = args
            B = control.sub(code, 1 - n, 1)
            base = control.sub(B, 0)
            hyp = control.sub(B, b) if base == [0, 0] else base
            return [[[], []]] + emit(r, g + [([], hyp)])
        q, r = args
        D, = control.prove(q, g)
        B = control.sub(D, b, 1)
        base = control.sub(B, 0)
        branch_g = g + [(base, B)]
        F = control.prove(r, branch_g)
        return [[D, F]] + emit(q, g) + emit(r, branch_g)

    packets = emit(proof, [([], [1, 1])])
    return list(reversed(packets)) + [goal]


def decode(data):
    """Untrusted inverse compiler; result is rechecked by the old tree kernel."""
    data = copy.deepcopy(data)
    goal = data.pop()

    def read(A, g):
        n = len(g)
        b = -n
        control.syntax(A, n, True)
        code, arg = data.pop()
        if type(code) is int:
            control.need(0 <= code < n)
            control.syntax(arg, n)
            base, B = g[code]
            control.need(control.sub(B, arg) == A)
            return [code, arg, read(base, g) if base else None]
        if code:
            p = read([code], g)
            B = control.sub(code, b, 1)
            base = control.sub(B, 0)
            r = read(arg, g + [(base, B)])
            out = [[], p, r]
            control.need(control.prove(out, g) == A)
            return out
        control.need(code == arg == [])
        matrix, = A
        B = control.sub(matrix, 1 - n, 1)
        base = control.sub(B, 0)
        hyp = control.sub(B, b) if base == [0, 0] else base
        return [matrix, read(control.sub(B, [0, b, 0]), g + [([], hyp)])]

    out = [goal, read(goal, [([], [1, 1])])]
    control.need(not data)
    control.check(out)
    return out


if __name__ == '__main__':
    print(json.dumps(convert(json.load(open(0))), separators=(',', ':')))
