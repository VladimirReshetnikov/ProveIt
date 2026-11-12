from pathlib import Path
BASE = Path(__file__).resolve().parent / 'reference'
OUT = Path(__file__).resolve().parent
for mode in ('canonical', 'raw', 'scalar'):
    source = (BASE / f'{mode}_checker.py').read_text()
    first = source.index('def shift_term(')
    last = source.index('\n\ndef reverse(', first)
    shared = '''def action(t, f, depth=0):
    if type(t) is int:
        return t if t <= depth else f(t - depth, depth)
    if type(t[0]) is str:
        extra = 0 if t[0] == '=' else 1 if t[0] == 'Q' else 2
        return [t[0]] + [action(a, f, depth + extra) for a in t[1:]]
'''
    if mode == 'scalar':
        shared += '''    if len(t) == 1:
        return [action(t[0], f, depth)]
'''
    shared += '''    return rec(action(t[0], f, depth), action(t[1], f, depth),
               action(t[2], f, depth + 1))


def shift(t, amount=1, depth=0):
    return action(t, lambda i, d: i + d + amount, depth)


def subst(t, images, depth=0):
    return action(t, lambda i, d: shift(images[i - 1], d)
                  if i <= len(images) else i + d - len(images), depth)
'''
    output = source[:first] + shared + source[last:]
    for old, new in [('shift_term(', 'shift('), ('shift_formula(', 'shift('),
                     ('subst_term(', 'subst('), ('subst_formula(', 'subst(')]:
        output = output.replace(old, new)
    (OUT / f'{mode}_shared.py').write_text(output)
