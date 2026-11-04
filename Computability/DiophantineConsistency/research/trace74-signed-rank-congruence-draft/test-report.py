#!/usr/bin/env python3
"""Test the actual runner's report policy without importing or running Lean."""
import ast, json
from pathlib import Path
import re
source=Path(__file__).with_name('run.py').read_text()
tree=ast.parse(source)
fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='check_reports')
ns={'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),'<copied-actual-policy>','exec'),ns);check=ns['check_reports']
a="'Trace74SignedRankCongruence.signed_dvd_of_mod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]"
b="'Trace74SignedRankCongruence.graph_signed_rank_congruence' depends on axioms: [propext, Classical.choice, Quot.sound]"
none="'Trace74SignedRankCongruence.signed_dvd_of_mod_eq' does not depend on any axioms"
cases={'valid':(a+'\n'+b,True),'wrapped':(a.replace(', ', ',\n ')+ '\n'+b,True),'none':(none+'\n'+b,True),'missing_first':(b,False),'missing_second':(a,False),'extra_text':(a+'\n'+b+'\nextra',False),'extra_report':(a+'\n'+b+'\n'+b,False),'wrong_name':(a.replace('signed_dvd_of_mod_eq','other')+'\n'+b,False),'reverse_order':(b+'\n'+a,False),'duplicate_axiom':(a.replace('propext,','propext, propext,')+'\n'+b,False),'unknown_axiom':(a.replace('propext','sorryAx')+'\n'+b,False),'empty_entry':(a.replace('propext,','propext,,')+'\n'+b,False),'trailing_comma':(a.replace('Quot.sound]','Quot.sound,]')+'\n'+b,False),'empty_list':(a.replace('propext, Classical.choice, Quot.sound','')+'\n'+b,False),'unclosed':(a[:-1]+'\n'+b,False)}
for name,(data,want) in cases.items():
 got=check(data)
 if got!=want:raise SystemExit(name+' policy failure')
print(json.dumps({'status':'PASS','cases':len(cases),'accepts':['valid','wrapped','none'],'scope':'static copied report-policy function only; no Lean invocation'},sort_keys=True))
