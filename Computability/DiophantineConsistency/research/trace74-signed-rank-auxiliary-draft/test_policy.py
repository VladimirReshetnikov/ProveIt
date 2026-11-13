#!/usr/bin/env python3
import ast,pathlib,re
p=pathlib.Path(__file__).with_name("run.py");tree=ast.parse(p.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="report_ok");ns={"re":re};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(p),"exec"),ns);test=ns["report_ok"]
names=["Trace74JoinedSquare.strong_and_auxiliary_indices_with_graph_residue"]
def fmt(n,a="propext"):return "'"+n+"' depends on axioms: ["+a+"]\n"
good=fmt(names[0]);cases=[(good,True),("'"+names[0]+"' does not depend on any axioms\n",True),("",False),(good+"noise",False),(good+good,False),(fmt("wrong"),False),(fmt(names[0],"sorryAx"),False),(fmt(names[0],"propext, propext"),False),(fmt(names[0],""),False),(fmt(names[0],"propext,"),False),(fmt(names[0],",propext"),False),(good+"warning: test",False)]
for raw,want in cases:assert test(raw,names)==want
names2=["Trace74SignedRankAuxiliary.graph_signed_rank_auxiliary"]
for raw,want in cases:assert test(raw.replace(names[0],names2[0]),names2)==want
print("PASS: %d report-policy controls" % (2*len(cases)))
