#!/usr/bin/env python3
"""Exercise the actual per-stage report parser without invoking Lean."""
import ast,json,re
from pathlib import Path
p=Path(__file__).with_name('run.py');tree=ast.parse(p.read_text());fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='report_ok');ns={'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),'<copied-actual-policy>','exec'),ns);check=ns['report_ok']
name='Trace74ArbitraryRoot.roots_of_representatives';a="'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]";none="'"+name+"' does not depend on any axioms"
cases={'valid':(a,True),'wrapped':(a.replace(', ', ',\n '),True),'none':(none,True),'missing':('',False),'extra_text':(a+'\nextra',False),'extra_report':(a+'\n'+a,False),'wrong_name':(a.replace(name,'other'),False),'duplicate_axiom':(a.replace('propext,','propext, propext,'),False),'unknown_axiom':(a.replace('propext','sorryAx'),False),'empty_entry':(a.replace('propext,','propext,,'),False),'trailing_comma':(a.replace('Quot.sound]','Quot.sound,]'),False),'empty_list':(a.replace('propext, Classical.choice, Quot.sound',''),False),'unclosed':(a[:-1],False)}
for key,(data,want) in cases.items():
 if check(data,name)!=want:raise SystemExit('policy mismatch '+key)
print(json.dumps({'status':'PASS','cases':len(cases),'scope':'actual copied report parser only; no Lean invocation'},sort_keys=True))
