from pathlib import Path

ROOT = Path(__file__).resolve().parent
COMMON = (ROOT / 'kernel_common.py.template').read_text()
OLD = '''        case ['tr', a, b, p, q]:
            term(a, n + 1)
            term(b, n + 1)
            e = infer(p, g, n)
            require(e[0] == '=')
            s, t = e[1:]
            require(infer(q, g, n) == ['=', sub(a, s), sub(b, s)])
            return ['=', sub(a, t), sub(b, t)]'''
NEW = '''        case ['tr', a, p, q]:
            term(a, n + 1)
            e = infer(p, g, n)
            f = infer(q, g, n)
            require(e[0] == f[0] == '=')
            s, t = e[1:]
            require(f[1] == sub(a, s))
            return ['=', f[2], sub(a, t)]'''
for name, rule in [('native_checker.py', OLD), ('one_context_checker.py', NEW)]:
    (ROOT / name).write_text(COMMON.replace('@@TRANSPORT@@', rule))

