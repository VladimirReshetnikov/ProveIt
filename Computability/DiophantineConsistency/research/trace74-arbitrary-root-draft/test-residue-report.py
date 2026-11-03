#!/usr/bin/env python3
"""Test the combined runner's actual report policy without running Lean."""
import ast,json,re
from pathlib import Path
source=Path(__file__).with_name('run-residue.py').read_text();tree=ast.parse(source)
fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='check_reports')
ns={'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),'<copied-actual-policy>','exec'),ns);check=ns['check_reports']
a="'Trace74FirstIndexResidue.graph_first_index_residue' depends on axioms: [propext, Classical.choice, Quot.sound]"
none="'Trace74FirstIndexResidue.graph_first_index_residue' does not depend on any axioms"
cases={'valid':(a,True),'wrapped':(a.replace(', ', ',\n '),True),'none':(none,True),'missing':('',False),'extra_text':(a+'\nextra',False),'extra_report':(a+'\n'+a,False),'wrong_name':(a.replace('graph_first_index_residue','other'),False),'duplicate_axiom':(a.replace('propext,','propext, propext,'),False),'unknown_axiom':(a.replace('propext','sorryAx'),False),'empty_entry':(a.replace('propext,','propext,,'),False),'trailing_comma':(a.replace('Quot.sound]','Quot.sound,]'),False),'empty_list':(a.replace('propext, Classical.choice, Quot.sound',''),False),'unclosed':(a[:-1],False)}
for name,(data,want) in cases.items():
 if check(data)!=want:raise SystemExit(name+' policy failure')
print(json.dumps({'status':'PASS','cases':len(cases),'scope':'copied actual report policy only; no Lean invocation'},sort_keys=True))
