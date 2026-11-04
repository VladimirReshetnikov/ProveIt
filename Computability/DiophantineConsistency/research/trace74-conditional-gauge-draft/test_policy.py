#!/usr/bin/env python3
import ast,pathlib,re
p=pathlib.Path(__file__).with_name('run.py');tree=ast.parse(p.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='check_reports');ns={'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(p),'exec'),ns);test=ns['check_reports'];name='Trace74ConditionalGauge.same_output_of_transport_equations'
def fmt(n,a='propext'):return "'"+n+"' depends on axioms: ["+a+"]\n"
good=fmt(name);cases=[(good,True),("'"+name+"' does not depend on any axioms\n",True),('',False),(good+'noise',False),(good+good,False),(fmt('wrong'),False),(fmt(name,'sorryAx'),False),(fmt(name,'propext, propext'),False),(fmt(name,''),False),(fmt(name,'propext,'),False),(fmt(name,',propext'),False),(good+'warning: test',False)]
for raw,want in cases:assert test(raw)==want
print('PASS: %d report-policy controls' % len(cases))
