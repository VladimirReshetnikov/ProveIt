#!/usr/bin/env python3
"""Mutation controls for actual runner policy functions; never invokes Lean."""
from pathlib import Path
from hashlib import sha256
import ast,json,os,re,sys,tempfile
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;SRC=H/'run-template.py';O=H/'observations/template-policy-attempt02'
PIN='38dbc2b7b2e7a6f8b932d69a5f6cec79e5113bd845cc2d2bc19b86856f33cb0f'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not O.exists() and sha(SRC)==PIN,'output exists or source drift')
tree=ast.parse(SRC.read_text());names={'sha','need','rel','diag','reports_ok','selected','check_copies','ensure_vacant','header_matches'}
nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names];need({x.name for x in nodes}==names,'function inventory')
ns={'Path':Path,'os':os,'re':re,'sha256':sha256,'SUFFIXES':('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(SRC),'exec'),ns)
def rejected(f):
 try:f()
 except RuntimeError:return True
 return False
report="'Trace75BFSHaltGraph.halt_zero_of_model_ports' depends on axioms: [propext, Classical.choice, Quot.sound]\n";ok=ns['reports_ok'];checks={}
hm=ns['header_matches'];checks['two_init_headers_accepted']=hm(['Init','Init','A','B'],['A','B']);checks['missing_init_rejected']=not hm(['A','B'],['A','B']);checks['added_import_rejected']=not hm(['Init','Init','A','B','C'],['A','B']);checks['reordered_import_rejected']=not hm(['Init','Init','B','A'],['A','B'])
checks['exact_report_accepted']=ok(report,'',report,'')
checks['missing_report_rejected']=not ok('','',report,'')
checks['duplicate_report_rejected']=not ok(report+report,'',report,'')
checks['unknown_axiom_rejected']=not ok(report.replace('Quot.sound','Quot.sound, unsafeAxiom'),'',report,'')
checks['unexpected_theorem_rejected']=not ok(report.replace('halt_zero_of_model_ports','other'),'',report,'')
checks['coded_warning_rejected']=not ok(report+'warning(lean.foo): issue\n','',report,'')
checks['coded_error_rejected']=not ok(report,'error(lean.foo): issue\n',report,'')
checks['sorry_rejected']=not ok(report.replace('Quot.sound','sorryAx'),'',report,'')
checks['extra_plain_output_rejected']=not ok(report+'extra\n','',report,'')
with tempfile.TemporaryDirectory(prefix='trace75-rebuild-policy-') as d:
 a=Path(d)/'a';b=Path(d)/'b';(a/'Foo').mkdir(parents=True);(b/'Foo').mkdir(parents=True)
 p=b/'Foo/Bar.olean';p.write_bytes(b'old');roots=[a,b];select=ns['selected']
 checks['outside_later_selected']=select('Foo.Bar',roots)==p
 shadow=a/'Foo/Bar.olean';shadow.write_bytes(b'new')
 checks['outside_shadow_detectable']=select('Foo.Bar',roots)!=p
 shadow.unlink();shadow.symlink_to(a/'missing')
 checks['dangling_shadow_rejected']=rejected(lambda:select('Foo.Bar',roots));shadow.unlink()
 src=Path(d)/'source.lean';src.write_bytes(b'original');copies={str(src):sha(src)}
 ns['check_copies'](copies);src.write_bytes(b'changed');checks['copied_source_drift_rejected']=rejected(lambda:ns['check_copies'](copies))
 src.write_bytes(b'original');other=Path(d)/'other.lean';other.write_bytes(b'original');src.unlink();src.symlink_to(other)
 checks['copied_source_same_byte_symlink_rejected']=rejected(lambda:ns['check_copies'](copies))
 stem=Path(d)/'out';ns['ensure_vacant'](stem);Path(str(stem)+'.olean.private').write_bytes(b'x')
 checks['companion_clobber_rejected']=rejected(lambda:ns['ensure_vacant'](stem))
need(all(checks.values()),'failed controls');need(sha(SRC)==PIN,'runner drift');O.mkdir(parents=True)
r={'status':'PASS','runner_sha256':PIN,'test_sha256':sha(__file__),'checks':checks,'scope':'actual runner functions tested in temporary directories; no Lean replay'}
(O/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','checks':len(checks),'sha256':sha(O/'result.json')}))
