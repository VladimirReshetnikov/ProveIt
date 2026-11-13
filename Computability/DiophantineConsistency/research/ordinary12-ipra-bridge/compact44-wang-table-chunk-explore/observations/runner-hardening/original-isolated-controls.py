import ast,hashlib,os,pathlib,re,subprocess,sys,tempfile
P=pathlib.Path;p=P('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-wang-table-chunk-explore/replay.py');s=p.read_text();assert hashlib.sha256(s.encode()).hexdigest()=='8d6e532541a7a06c129e58c8f478ec945338b18bb2b22906ebdcb3a17ff2a664';tree=ast.parse(s); names={'need','H','rec','slots','check'};nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in names];assert {n.name for n in nodes}==names
ns={'Path':P,'hashlib':hashlib,'os':os,'SUF':('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(p),'exec'),ns)
def reject(f):
 try:f()
 except ValueError:return True
 return False
with tempfile.TemporaryDirectory(prefix='wang-old-runner-controls-') as x:
 root=P(x);lib=root/'lib';pkg=root/'pkg';lib.mkdir();pkg.mkdir();(pkg/'Input.olean').write_bytes(b'original');choices=[q for q in (lib/'Input.olean',pkg/'Input.olean') if q.is_file()];chosen=choices[0];guard=ns['slots'](P(str(chosen)[:-6]));(pkg/'Input.olean').write_bytes(b'changed');assert reject(lambda:ns['check'](guard));(pkg/'Input.olean').write_bytes(b'original');(pkg/'Input.olean.private').write_bytes(b'new');assert reject(lambda:ns['check'](guard));(pkg/'Input.olean.private').unlink();(lib/'Input.olean').write_bytes(b'shadow');ns['check'](guard);new=next(q for q in (lib/'Input.olean',pkg/'Input.olean') if q.is_file());assert chosen!=new
checks=[]
for node in ast.walk(tree):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='need' and node.args and isinstance(node.args[0],ast.UnaryOp) and 're.search' in ast.unparse(node.args[0]) and 'sorryAx' in ast.unparse(node.args[0]):checks.append(node.args[0])
assert len(checks)==1
pred=compile(ast.Expression(checks[0]),str(p),'eval');accept=lambda txt:eval(pred,{'re':re},{'text':txt})
assert accept("'test' depends on axioms: [Unexpected.axiom]\n") and accept('') and not accept('warning: test\n') and not accept("'test' depends on axioms: [sorryAx]\n")
r=subprocess.run([sys.executable,'-O','-I','-S',str(p)],capture_output=True,text=True,timeout=10);assert r.returncode!=0 and 'optimized Python rejected' in r.stderr
print({'guard_rejects_changed_chosen_object':True,'guard_rejects_added_chosen_companion':True,'shadow_changed_provider_while_guards_passed':True,'diagnostics_accept_unexpected_named_axiom':True,'diagnostics_accept_missing_reports':True,'diagnostics_reject_warning_and_sorryAx':True,'optimized_exit':r.returncode,'lean_launched':False})
