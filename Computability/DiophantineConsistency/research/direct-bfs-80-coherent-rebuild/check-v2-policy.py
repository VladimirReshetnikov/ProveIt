#!/usr/bin/env python3
"""Exercise the actual v2 helper AST without importing or launching its runner."""
from pathlib import Path
from hashlib import sha256
import ast, json, os, re, tempfile
H=Path(__file__).resolve().parent
runner=H/'run-v2.py'
tree=ast.parse(runner.read_text())
names={'need','sha','present','files','hashes','ensure_vacant','check_records','diagnostics_ok','endpoint_axioms_ok'}
selected=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names]
assert {n.name for n in selected}==names
ns={'Path':Path,'sha256':sha256,'os':os,'re':re,
    'SUFFIXES':('.olean','.olean.hash','.olean.private','.olean.private.hash','.olean.server','.olean.server.hash','.ilean','.ilean.hash','.ir','.ir.hash'),
    'THEOREMS':('standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency')}
exec(compile(ast.Module(body=selected,type_ignores=[]),str(runner),'exec'),ns)
passed=[]
def ok(name, condition):
    if not condition:raise RuntimeError('FAILED '+name)
    passed.append(name)
def fails(name,fn):
    try:fn()
    except (RuntimeError,OSError):passed.append(name);return
    raise RuntimeError('not rejected '+name)
diag=ns['diagnostics_ok'];axioms=ns['endpoint_axioms_ok']
ok('clean diagnostics',diag('ordinary output\n'))
for i,t in enumerate(['warning: bad','error: bad','warning(lean.unusedVariables): bad','error(lean.unknownIdentifier): bad','sorryAx']):ok('diagnostic rejected '+str(i),not diag(t))
base='\n'.join("'DirectBFS80FixedIPRA.%s' depends on axioms: [propext, Classical.choice, Quot.sound]"%n for n in ns['THEOREMS'])
ok('allowed axiom reports',axioms(base))
noaxiom='\n'.join("'DirectBFS80FixedIPRA.%s' does not depend on any axioms"%n for n in ns['THEOREMS'])
ok('empty axiom reports',axioms(noaxiom))
ok('missing report rejected',not axioms(base.split('\n',1)[1]))
ok('duplicate report rejected',not axioms(base+'\n'+base.split('\n')[0]))
ok('unexpected axiom rejected',not axioms(base.replace('Quot.sound','Quot.sound, rogueAx',1)))
with tempfile.TemporaryDirectory(prefix='bfs-runner-v2-mutations-') as d:
    d=Path(d);stem=d/'unit';obj=d/'unit.olean';other=d/'other';other.write_bytes(b'A');obj.symlink_to(other)
    expected=ns['files'](stem);ns['check_records'](stem,expected,'link');passed.append('original link accepted')
    other2=d/'other2';other2.write_bytes(b'A');obj.unlink();obj.symlink_to(other2)
    fails('equal bytes changed link target rejected',lambda:ns['check_records'](stem,expected,'link'))
    obj.unlink();obj.write_bytes(b'A')
    fails('link replaced by regular rejected',lambda:ns['check_records'](stem,expected,'link'))
    obj.unlink();obj.symlink_to(d/'missing')
    fails('dangling entry rejected by files',lambda:ns['files'](stem))
    fails('dangling output collision rejected',lambda:ns['ensure_vacant'](stem))
    obj.unlink();obj.mkdir();fails('directory rejected by files',lambda:ns['files'](stem));fails('directory collision rejected',lambda:ns['ensure_vacant'](stem));obj.rmdir()
    ns['ensure_vacant'](stem);passed.append('vacant output accepted')
    obj.write_bytes(b'A');built=ns['files'](stem);ns['check_records'](stem,built,'regular');passed.append('regular built accepted')
    obj.write_bytes(b'B');fails('built content drift rejected',lambda:ns['check_records'](stem,built,'regular'))
    obj.unlink();obj.symlink_to(other);fails('built symlink substitution rejected',lambda:ns['check_records'](stem,built,'regular'))
    obj.unlink();obj.write_bytes(b'A');extra=d/'unit.ilean';extra.write_bytes(b'extra');fails('unexpected companion rejected',lambda:ns['check_records'](stem,built,'regular'))
print(json.dumps({'status':'PASS','runner_sha256':sha256(runner.read_bytes()).hexdigest(),'checks':passed},indent=2))
