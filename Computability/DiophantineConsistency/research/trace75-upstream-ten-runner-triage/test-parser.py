#!/usr/bin/env python3
"""Exercise the allowlisted static path parser with isolated fixtures."""
import ast,json,tempfile,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent;source=h/'check.py';tree=ast.parse(source.read_text())
names={'need','value','paths_from_runner','first_now'}
nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names]
if {n.name for n in nodes}!=names:raise SystemExit('parser functions missing')
ns={'ast':ast,'Path':Path};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(source),'exec'),ns)
def attempt(text):
    with tempfile.TemporaryDirectory(prefix='trace75-runner-parser-test-') as t:
        p=Path(t)/'runner.py';p.write_text(text)
        try:return ns['paths_from_runner'](p)
        except (RuntimeError,TypeError,ValueError,KeyError):return None
good="lib=Path('/lib')\nextra=[Path('/one')]\nextra += [lib / ('X/'+n+'.olean') for n in ['A','B']]\nextra.append(Path('/last'))\npins={}\n"
tests={'accept_literal_and_comprehension':attempt(good)==[Path('/one'),Path('/lib/X/A.olean'),Path('/lib/X/B.olean'),Path('/last')],
       'reject_unrecognized_call':attempt("extra=[__import__('os')]\npins={}\n") is None,
       'reject_late_append':attempt("extra=[Path('/x')]\npins={}\nextra.append(Path('/y'))\n") is None,
       'reject_late_extend':attempt("extra=[Path('/x')]\npins={}\nextra.extend([Path('/y')])\n") is None,
       'reject_missing_capture':attempt("extra=[Path('/x')]\n") is None,
       'reject_filtered_comprehension':attempt("extra=[Path(n) for n in ['/x'] if n]\npins={}\n") is None}
with tempfile.TemporaryDirectory(prefix='trace75-path-policy-test-') as t:
    root=Path(t);a=root/'a';b=root/'b';a.mkdir();b.mkdir();(a/'N').mkdir();(b/'N').mkdir()
    (b/'N'/'M.olean').write_bytes(b'x');(b/'Top.olean').write_bytes(b'x')
    tests['namespace_shadow_stops_search']=ns['first_now']('N.M',[a,b]) is None
    tests['top_level_search_continues']=ns['first_now']('Top',[a,b])==b/'Top.olean'
print(json.dumps({'status':'PASS' if all(tests.values()) else 'FAIL','tests':tests,
                  'scope':'isolated parser policy; no historical runner execution or Lean'},sort_keys=True))
raise SystemExit(0 if all(tests.values()) else 1)
