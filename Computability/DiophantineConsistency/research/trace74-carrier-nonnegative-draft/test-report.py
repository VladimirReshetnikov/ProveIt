#!/usr/bin/env python3
"""Verify actual copied multi-report policy without running Lean."""
import ast,json,re
from pathlib import Path
s=Path(__file__).with_name('run.py').read_text();t=ast.parse(s);f=next(x for x in t.body if isinstance(x,ast.FunctionDef) and x.name=='report_ok');ns={'re':re};exec(compile(ast.Module(body=[f],type_ignores=[]),'<copied-policy>','exec'),ns);check=ns['report_ok']
names=['Trace74CarrierNonnegative.graph_F_carrier_bound','Trace74CarrierNonnegative.graph_B_nonnegative']
lines=["'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names];base='\n'.join(lines)
cases={'valid':(base,True),'wrapped':(base.replace(', ', ',\n '),True),'missing':('\n'.join(lines[1:]),False),'duplicate':(base+'\n'+lines[-1],False),'garbage':(base+'\nextra',False),'wrong':(base.replace(names[1],'wrong'),False),'order':('\n'.join(reversed(lines)),False),'dupe_axiom':(base.replace('propext,','propext, propext,',1),False),'unknown':(base.replace('propext','sorryAx',1),False),'empty':(base.replace('propext,','propext,,',1),False),'trailing_comma':(base.replace('Quot.sound]','Quot.sound,]',1),False),'empty_list':(base.replace('propext, Classical.choice, Quot.sound','',1),False),'unclosed':(base[:-1],False)}
for k,(text,want) in cases.items():
 if check(text,names)!=want:raise SystemExit('policy mismatch '+k)
print(json.dumps({'status':'PASS','cases':len(cases),'scope':'copied policy only; no Lean invocation'},sort_keys=True))
