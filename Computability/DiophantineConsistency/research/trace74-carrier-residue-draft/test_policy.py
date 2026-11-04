#!/usr/bin/env python3
import ast,pathlib,re
p=pathlib.Path(__file__).with_name('run.py');tree=ast.parse(p.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='report_ok');ns={'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(p),'exec'),ns);test=ns['report_ok']
names=['Trace74CarrierResidue.graph_carrier_h_divides_HDB','Trace74CarrierResidue.reduce_carrier_mod_h','Trace74CarrierResidue.graph_explicit_carrier_residue']
def fmt(n,a='propext'):return "'"+n+"' depends on axioms: ["+a+"]\n"
good=''.join(map(fmt,names));cases=[(good,True),(''.join("'"+n+"' does not depend on any axioms\n" for n in names),True),(fmt(names[0])+fmt(names[1]),False),(good+'noise',False),(good+fmt(names[2]),False),(fmt('wrong')+fmt(names[1])+fmt(names[2]),False),(fmt(names[0],'sorryAx')+fmt(names[1])+fmt(names[2]),False),(fmt(names[0],'propext, propext')+fmt(names[1])+fmt(names[2]),False),(fmt(names[0],'')+fmt(names[1])+fmt(names[2]),False),(fmt(names[0],'propext,')+fmt(names[1])+fmt(names[2]),False),(fmt(names[0],',propext')+fmt(names[1])+fmt(names[2]),False),(fmt(names[1])+fmt(names[0])+fmt(names[2]),False),(good+'warning: test',False)]
for raw,want in cases:assert test(raw,names)==want
print('PASS: %d report-policy controls' % len(cases))
