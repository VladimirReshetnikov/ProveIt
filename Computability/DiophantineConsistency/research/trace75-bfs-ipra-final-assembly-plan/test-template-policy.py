#!/usr/bin/env python3
"""Exercise selected held-template policies without reading any parent."""
import ast,json,os,re,subprocess,sys,tempfile
from hashlib import sha256
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent; runner=h/'run-template.py'
source=runner.read_text();tree=ast.parse(source)
names={'sha','need','diag','stage_reports_ok','header_matches','check_copies','ensure_vacant','parse'}
nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names]
if {n.name for n in nodes}!=names:raise SystemExit('missing policy functions')
ns={'re':re,'os':os,'Path':Path,'sha256':sha256,
    'SUFFIXES':('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')}
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(runner),'exec'),ns)
ok=ns['stage_reports_ok'];header=ns['header_matches']
base="'Trace75BFSSyntax.literal_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
tests={
 'good_report':ok('Trace75BFSSyntax',base,''),
 'reject_missing_report':not ok('Trace75BFSSyntax','', ''),
 'reject_extra_report':not ok('Trace75BFSSyntax',base+base,''),
 'reject_unexpected_text':not ok('Trace75BFSSyntax',base+'extra text\n',''),
 'reject_warning':not ok('Trace75BFSSyntax',base+'warning: x\n',''),
 'reject_sorry':not ok('Trace75BFSSyntax',base.replace('propext','sorryAx'),''),
 'reject_unknown_axiom':not ok('Trace75BFSSyntax',base.replace('propext','unapproved'),''),
 'reject_stderr':not ok('Trace75BFSSyntax',base,'unexpected'),
 'accept_valid_header':header(['Init','A','B'],['A','B']),
 'reject_missing_init':not header(['A','B'],['A','B']),
 'reject_reordered_header':not header(['Init','B','A'],['A','B']),
}
def raises(f):
    try:f()
    except (RuntimeError,KeyError,ValueError):return True
    return False
with tempfile.TemporaryDirectory(prefix='trace75-assembly-policy-') as td:
    root=Path(td); copied=root/'copy';copied.write_bytes(b'good')
    digest=sha256(b'good').hexdigest(); record={str(copied):digest}
    tests['accept_source_copy']=not raises(lambda:ns['check_copies'](record))
    copied.write_bytes(b'changed')
    tests['reject_mutated_source']=raises(lambda:ns['check_copies'](record))
    copied.unlink();target=root/'target';target.write_bytes(b'good');copied.symlink_to(target)
    tests['reject_same_bytes_symlink']=raises(lambda:ns['check_copies'](record))
    stem=root/'FreshOutput';tests['accept_vacant_output']=not raises(lambda:ns['ensure_vacant'](stem))
    (root/'FreshOutput.olean.server').write_bytes(b'occupied')
    tests['reject_any_output_companion']=raises(lambda:ns['ensure_vacant'](stem))
    parse=ns['parse']; mapping={'/tmp/object':'Module'}
    tests['accept_header_batch']=parse('BEGIN /tmp/object\nIMPORT Init\nEND\n',mapping)=={'Module':['Init']}
    tests['reject_duplicate_header']=raises(lambda:parse('BEGIN /tmp/object\nEND\nBEGIN /tmp/object\nEND\n',mapping))
    tests['reject_missing_header']=raises(lambda:parse('',mapping))
proc=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight-only'],capture_output=True,text=True)
tests['held_parent_refusal']=proc.returncode!=0 and 'parent result and outer must be pinned' in proc.stderr
result={'status':'PASS' if all(tests.values()) else 'FAIL','tests':tests,
        'scope':'selected policies and held-parent refusal only; no parent read and no Lean'}
print(json.dumps(result,sort_keys=True))
raise SystemExit(0 if result['status']=='PASS' else 1)
