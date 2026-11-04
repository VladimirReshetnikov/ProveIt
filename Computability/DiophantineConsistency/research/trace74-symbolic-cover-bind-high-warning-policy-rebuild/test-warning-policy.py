#!/usr/bin/env python3
"""Exercise the actual exact-warning validator; no Lean invocation."""
from pathlib import Path
from hashlib import sha256
import ast, json, os, sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;source=H/'run.py';out=H/'observations/warning-policy-attempt01'
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
PIN='a476d99ba80220c01acf4cafe53b27524ea671fafebeb6ea9e5e7c5dcda2e971'
if os.path.lexists(out) or sha(source)!=PIN:raise SystemExit('output exists or runner drift')
tree=ast.parse(source.read_text());nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='reports_exact_allowed_warning']
if len(nodes)!=1:raise SystemExit('validator missing or duplicate')
ns={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(source),'exec'),ns);check=ns['reports_exact_allowed_warning'];path=Path('/tmp/example/src/Trace74CoverBindHigh.lean');names=['Trace74CoverBindHigh.cover_nat']
warning=str(path)+':14:50: warning: exponent 4393 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold\n';report="'Trace74CoverBindHigh.cover_nat' depends on axioms: [propext, Classical.choice, Quot.sound]\n";good=warning+report
checks={'exact_accepted':check(good,'',names,path), 'missing_warning_rejected':not check(report,'',names,path), 'duplicate_warning_rejected':not check(warning+good,'',names,path), 'wrong_path_rejected':not check(good.replace('/tmp/example/','/tmp/other/'),'',names,path), 'wrong_line_rejected':not check(good.replace(':14:50:',':13:50:'),'',names,path), 'changed_text_rejected':not check(good.replace('was not evaluated','was evaluated'),'',names,path), 'other_warning_rejected':not check(good+'warning: other\n','',names,path), 'extra_axiom_rejected':not check(good.replace('[propext, Classical.choice, Quot.sound]','[propext, Classical.choice, Quot.sound, sorryAx]'),'',names,path), 'missing_report_rejected':not check(warning,'',names,path), 'extra_report_rejected':not check(good+report,'',names,path), 'stderr_rejected':not check(good,'unexpected',names,path), 'wrong_name_rejected':not check(good,'',['other'],path)}
if not all(checks.values()) or sha(source)!=PIN:raise SystemExit('failed mutation controls '+repr(checks))
out.mkdir(parents=True);r={'status':'PASS','runner_sha256':PIN,'test_sha256':sha(__file__),'checks':checks,'scope':'actual exact-warning function; synthetic strings, no Lean'}
with (out/'result.json').open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
print(sha(out/'result.json'))
