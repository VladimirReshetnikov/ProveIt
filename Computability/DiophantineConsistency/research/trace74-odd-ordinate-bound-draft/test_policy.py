#!/usr/bin/env python3
"""Exercise the exact held runner's report parser without executing the runner."""
import ast, pathlib, re
p=pathlib.Path(__file__).with_name('run.py')
tree=ast.parse(p.read_text()); fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='report_ok')
ns={'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(p),'exec'),ns);test=ns['report_ok']
names=['Trace74OddOrdinateBound.ordinate_three','Trace74OddOrdinateBound.graph_ordinate_lower']
def fmt(n,a='propext'):return "'"+n+"' depends on axioms: ["+a+"]\n"
good=fmt(names[0])+fmt(names[1]);cases=[('valid',good,True),('none',"'"+names[0]+"' does not depend on any axioms\n"+fmt(names[1]),True),('missing',fmt(names[0]),False),('extra',good+'noise',False),('duplicate report',good+fmt(names[1]),False),('wrong report',fmt('wrong')+fmt(names[1]),False),('unknown axiom',fmt(names[0],'sorryAx')+fmt(names[1]),False),('duplicate axiom',fmt(names[0],'propext, propext')+fmt(names[1]),False),('empty axiom',fmt(names[0],'')+fmt(names[1]),False),('trailing empty',fmt(names[0],'propext,')+fmt(names[1]),False),('leading empty',fmt(names[0],',propext')+fmt(names[1]),False),('reordered',fmt(names[1])+fmt(names[0]),False),('warning',good+'warning: test',False)]
for label,raw,want in cases:
 assert test(raw,names)==want,label
print('PASS: %d report-policy controls' % len(cases))
