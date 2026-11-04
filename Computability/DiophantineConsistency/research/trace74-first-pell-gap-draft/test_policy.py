#!/usr/bin/env python3
import ast,pathlib,re
p=pathlib.Path(__file__).with_name("run.py");tree=ast.parse(p.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="report_ok");ns={"re":re};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(p),"exec"),ns);test=ns["report_ok"]
names=["Trace74FirstPellGap.graph_first_pell_gap"]
def fmt(n,a="propext"):return "'"+n+"' depends on axioms: ["+a+"]\n"
good=fmt(names[0]);cases=[(good,True),("'"+names[0]+"' does not depend on any axioms\n",True),("",False),(good+"noise",False),(good+good,False),(fmt("wrong"),False),(fmt(names[0],"sorryAx"),False),(fmt(names[0],"propext, propext"),False),(fmt(names[0],""),False),(fmt(names[0],"propext,"),False),(fmt(names[0],",propext"),False),(good+"warning: test",False)]
for raw,want in cases:assert test(raw,names)==want
print("PASS: %d report-policy controls" % len(cases))
