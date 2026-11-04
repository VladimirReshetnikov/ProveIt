#!/usr/bin/env python3
import ast, pathlib, re

p = pathlib.Path(__file__).with_name('run.py')
tree = ast.parse(p.read_text())
assignment = next(n for n in tree.body if isinstance(n, ast.Assign)
                  and any(isinstance(t, ast.Subscript) and isinstance(t.value, ast.Name)
                          and t.value.id == 'env' and isinstance(t.slice, ast.Constant)
                          and t.slice.value == 'LEAN_PATH' for t in n.targets))
assert ast.unparse(assignment.value) == "':'.join(map(str, (lib, NG, YS, NOSMALL, R5GRAPH, REDUCTION, PROJECTION, SGROWTH, ODDFIVE, FIFTH, GRAPH, UPPER, ORDER, RESIDUE, CARRIER, ODD, FOLD, ADJ, PELL, ROOTS, BASE, SCALAR, GROWTH, PACK)))"
fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'report_ok')
ns = {'re': re}
exec(compile(ast.Module(body=[fn], type_ignores=[]), str(p), 'exec'), ns)
test = ns['report_ok']
stages = [['Trace74N5R7GraphGrowth.same_tuple_growth']]
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
