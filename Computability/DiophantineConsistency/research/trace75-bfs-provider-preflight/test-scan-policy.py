#!/usr/bin/env python3
"""Exercise selected search and strict serialized-record parsing without Lean."""
from pathlib import Path
from hashlib import sha256
import ast,json,os,re,sys,tempfile
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;SRC=H/'scan-v2.py';OUT=H/'observations/policy-attempt01'
PIN='c8e55712c29c8fb60de059c6451ffc5a4aa93319c3cfe20c70952837b4e1e2e2'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(SRC)==PIN,'scanner drift');need(not OUT.exists(),'output exists')
tree=ast.parse(SRC.read_text()); names={'need','selected','parse'};nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names]
need({n.name for n in nodes}==names,'function inventory')
ns={'Path':Path,'os':os,'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(SRC),'exec'),ns)
def rejects(fn):
 try:fn()
 except RuntimeError:return True
 return False
checks={}
with tempfile.TemporaryDirectory(prefix='trace75-resolution-policy-') as d:
 a=Path(d)/'a';b=Path(d)/'b';(a/'Foo').mkdir(parents=True);(b/'Foo').mkdir(parents=True)
 p=b/'Foo/Bar.olean';p.write_bytes(b'late');roots=[a,b];select=ns['selected']
 checks['later_selected']=select('Foo.Bar',roots)==p
 shadow=a/'Foo/Bar.olean';shadow.write_bytes(b'early')
 checks['new_shadow_changes_selection']=select('Foo.Bar',roots)==shadow
 shadow.unlink();shadow.symlink_to(a/'missing')
 checks['dangling_shadow_rejected']=rejects(lambda:select('Foo.Bar',roots))
 checks['invalid_module_rejected']=rejects(lambda:select('../etc',roots))
parse=ns['parse'];mapping={'/a':'A','/b':'B'}
checks['valid_records_accepted']=parse('BEGIN /a\nIMPORT Foo\nEND\nBEGIN /b\nEND\n',mapping)=={'A':['Foo'],'B':[]}
checks['missing_record_rejected']=rejects(lambda:parse('BEGIN /a\nEND\n',mapping))
checks['duplicate_record_rejected']=rejects(lambda:parse('BEGIN /a\nEND\nBEGIN /a\nEND\nBEGIN /b\nEND\n',mapping))
checks['incomplete_record_rejected']=rejects(lambda:parse('BEGIN /a\nEND\nBEGIN /b\n',mapping))
checks['unexpected_line_rejected']=rejects(lambda:parse('BEGIN /a\nBAD\nEND\n',mapping))
need(all(checks.values()),'policy test failed');need(sha(SRC)==PIN,'scanner changed')
OUT.mkdir(parents=True);result={'status':'PASS','scanner_sha256':PIN,'test_sha256':sha(__file__),'checks':checks,'scope':'unit controls on scanner functions; no Lean header or ancestry scan'}
(OUT/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','checks':len(checks),'sha256':sha(OUT/'result.json')}))
