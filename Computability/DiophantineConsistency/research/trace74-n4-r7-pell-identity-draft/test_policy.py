#!/usr/bin/env python3
import ast, pathlib, re

p = pathlib.Path(__file__).with_name('run.py')
tree = ast.parse(p.read_text())
fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'report_ok')
ns = {'re': re}
exec(compile(ast.Module(body=[fn], type_ignores=[]), str(p), 'exec'), ns)
test = ns['report_ok']
stages = [['Trace74N4R7PellIdentity.ordinate_seven']]
def fmt(name, axioms='propext'):
    return "'" + name + "' depends on axioms: [" + axioms + "]\n"
count = 0
for names in stages:
    good = ''.join(map(fmt, names))
    cases = [
        (good, True),
        (''.join("'" + n + "' does not depend on any axioms\n" for n in names), True),
        ('', False), (good + 'noise', False), (good + fmt(names[-1]), False),
        (fmt('wrong') + ''.join(map(fmt, names[1:])), False),
        (fmt(names[0], 'sorryAx') + ''.join(map(fmt, names[1:])), False),
        (fmt(names[0], 'propext, propext') + ''.join(map(fmt, names[1:])), False),
        (fmt(names[0], '') + ''.join(map(fmt, names[1:])), False),
        (fmt(names[0], 'propext,') + ''.join(map(fmt, names[1:])), False),
        (fmt(names[0], ',propext') + ''.join(map(fmt, names[1:])), False),
        (good + 'warning: test', False),
    ]
    cases += [(''.join(fmt(n) for j, n in enumerate(names) if j != i), False)
              for i in range(len(names))]
    for raw, want in cases:
        assert test(raw, names) == want
        count += 1
print('PASS: %d report-policy controls' % count)
