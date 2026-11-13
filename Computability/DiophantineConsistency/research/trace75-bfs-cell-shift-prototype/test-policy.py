#!/usr/bin/env python3
"""Exercise the actual support runner policy functions without invoking Lean."""
from pathlib import Path
from hashlib import sha256
import ast,json,os,re,sys,tempfile
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;SRC=H/'run.py';O=H/'observations/policy-attempt01';PIN='019aed0d7e29601dfd3728dbe329fb26f0030a006b0fa0620d1e2017aaa17095'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(SRC)==PIN and not O.exists(),'runner drift or output exists');tree=ast.parse(SRC.read_text());names={'need','rel','selected','report_ok','check_root','check_clients','parse_header','sha'};nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names];need({x.name for x in nodes}==names,'function inventory');ns={'Path':Path,'os':os,'re':re,'sha256':sha256,'SUFFIXES':('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(SRC),'exec'),ns)
def reject(f):
 try:f()
 except RuntimeError:return True
 return False
report="'Trace75BFSCellShift.graph_cell_shift' depends on axioms: [propext, Classical.choice, Quot.sound]\n";ok=ns['report_ok'];checks={'exact_report':ok(report,''),'missing_report_rejected':not ok('',''),'duplicate_report_rejected':not ok(report+report,''),'unknown_axiom_rejected':not ok(report.replace('Quot.sound','unsafeAxiom'),''),'warning_rejected':not ok(report,'warning(lean.foo): x\n'),'sorry_rejected':not ok(report.replace('Quot.sound','sorryAx'),'')}
with tempfile.TemporaryDirectory(prefix='trace75-carry-policy-') as d:
 root=Path(d)/'root';lib=Path(d)/'lib';root.mkdir();(lib/'Foo').mkdir(parents=True);p=lib/'Foo/Bar.olean';p.write_bytes(b'x')
 checks['later_selected']=ns['selected']('Foo.Bar',[root,lib])==p
 (root/'Foo').mkdir();shadow=root/'Foo/Bar.olean';shadow.write_bytes(b'y');checks['shadow_detected']=ns['selected']('Foo.Bar',[root,lib])!=p;checks['root_shadow_rejected']=reject(lambda:ns['check_root'](root,{'Trace75BFSCellShift.lean','Trace75BFSCellShift.olean'}));shadow.unlink();shadow.symlink_to(root/'missing');checks['dangling_shadow_rejected']=reject(lambda:ns['selected']('Foo.Bar',[root,lib]))
 client=Path(d)/'client';client.mkdir();source=client/'M.lean';obj=client/'M.olean';source.write_bytes(b's');obj.write_bytes(b'o');items=[(client,'M',sha(source),sha(obj))]
 ns['check_clients'](items);obj.write_bytes(b'changed');checks['client_object_drift_rejected']=reject(lambda:ns['check_clients'](items));obj.write_bytes(b'o');source.write_bytes(b'changed');checks['client_source_drift_rejected']=reject(lambda:ns['check_clients'](items));source.write_bytes(b's');obj.unlink();alternate=Path(d)/'same-object';alternate.write_bytes(b'o');obj.symlink_to(alternate);checks['client_same_bytes_object_symlink_rejected']=reject(lambda:ns['check_clients'](items));obj.unlink();obj.write_bytes(b'o');source.unlink();alternate_source=Path(d)/'same-source';alternate_source.write_bytes(b's');source.symlink_to(alternate_source);checks['client_same_bytes_source_symlink_rejected']=reject(lambda:ns['check_clients'](items));source.unlink();source.write_bytes(b's');(client/'M.olean.private').write_bytes(b'extra');checks['client_companion_rejected']=reject(lambda:ns['check_clients'](items))
 path=Path('/tmp/example.olean');hdr='BEGIN '+str(path)+'\nIMPORT Init\nEND\n';checks['valid_header']=ns['parse_header'](hdr,path)==['Init'];checks['missing_end_rejected']=reject(lambda:ns['parse_header']('BEGIN '+str(path)+'\nIMPORT Init\n',path));checks['bad_import_rejected']=reject(lambda:ns['parse_header']('BEGIN '+str(path)+'\nIMPORT ../bad\nEND\n',path))
need(all(checks.values()) and sha(SRC)==PIN,'policy failure or drift');O.mkdir(parents=True);r={'status':'PASS','runner_sha256':PIN,'test_sha256':sha(__file__),'checks':checks,'scope':'actual runner policy functions in temporary directories; no Lean'};(O/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','checks':len(checks),'sha256':sha(O/'result.json')}))
