from pathlib import Path
import ast,hashlib,json,re
B=Path('/tmp/zfc-source-rotation240');O=Path('/tmp/zfc243-source-bridge/check-v2.py');H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return dict(path=str(p),sha256=sha(p))
count=0;inputs={}
def ck(ok,msg):
 global count
 count+=1
 if not ok:raise AssertionError(msg)
def pin(p,h):
 p=Path(p).resolve();ck(sha(p)==h,'Changed '+str(p));ck(str(p)not in inputs or inputs[str(p)]==h,'Conflict');inputs[str(p)]=h
pin(B/'check.py','163d9ba03ee5b6bf0edff594eb73c4a205d7d71561059cad60a2ad1807028e1e')
pin(B/'boundary.json','e6cfe81c25e032dfebcd0969d10982292a5d984097b8c9f4c15a67e1fc67809e')
new=ast.parse((B/'check.py').read_text());old=ast.parse(O.read_text())
for name in ['run','post','first','providers','reports']:
 a=next(n for n in ast.walk(new) if isinstance(n,ast.FunctionDef) and n.name==name)
 z=next(n for n in ast.walk(old) if isinstance(n,ast.FunctionDef) and n.name==name)
 ck(ast.dump(a)==ast.dump(z),'Unchanged execution/provider function '+name)
const={n.targets[0].id:ast.literal_eval(n.value) for n in new.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and isinstance(n.value,(ast.Constant,ast.List,ast.Dict,ast.Set))}
b=json.loads((B/'boundary.json').read_text());ck(set(b['parents'])=={'source'},'Single actual parent')
for q in b['static_inputs']:pin(q['path'],q['sha256'])
p=b['parents']['source'];pin(p['path'],p['sha256']);r=json.loads(Path(p['path']).read_text())
ck(p['sha256']=='cfdc9eda5d94383b6c2dd526a9a5f766bf7a97d7d47a1e30675055f7644dd701','Exact selected actual')
ck(r['status']=='PASS' and r['prepare_only']is False and r['before']==r['after'] and (r['named_axiom_probes'],r['callers'],r['warnings'])==(9,10,0),'Actual outcome')
for path,h in r['before'].items():pin(path,h)
for c in r['commands']:
 pin(c['log'],c['log_sha256']);ck(Path(c['log']).read_text()==c['output'] and c['exit_code']==0 and not c['timed_out'] and c['interrupted']is None,'Parent raw command')
f=r['fresh_modules'][0];pin(f['path'],f['sha256']);ck(r['source_pass_object']==dict(f,source_command_index=0) and r['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']},'Parent captures')
fields=['module','source','source_sha256','object','object_sha256'];pool={q['module']:{k:q[k]for k in fields}for q in r['reused_modules']}
pool[f['module']]=dict(module=f['module'],source=r['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])
ck({q['module']:q for q in b['reused_modules']}==pool and len(pool)==9,'Exact parent union')
ck(b['compiler']==r['compiler'] and b['toolchain_providers']==[{k:q[k]for k in ['module','object','object_sha256']}for q in r['toolchain_providers']],'Exact tools/compiler')
pin(b['compiler']['path'],b['compiler']['sha256'])
for q in b['reused_modules']:
 for k in ['source','object']:pin(q[k],q[k+'_sha256'])
for q in b['toolchain_providers']:pin(q['object'],q['object_sha256'])
imp=lambda p:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
seen=set()
def visit(m):
 if m=='Init':return
 ck(m in pool,'Unselected source import')
 if m in seen:return
 seen.add(m)
 for c in imp(pool[m]['source']):visit(c)
S=B/'SourceRotation240.lean';A=B/'Audit.lean';pin(S,const['SOURCE_SHA']);pin(A,const['AUDIT_SHA'])
for m in imp(S):visit(m)
ck(seen==set(pool) and imp(S)==['BusyBeaver.ZFC.SourceRotation244'],'Source DFS')
ck(imp(A)==[const['MODULE']] and len(re.findall(r'^example\b',A.read_text(),re.M))==13,'Typed census')
ck(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[const['PREFIX']+n for n in const['PROBES']] and len(const['PROBES'])==10,'Named census')
ck(all(sha(p)==h for p,h in inputs.items()),'Stable inputs')
receipt=dict(status='SOURCE_ONLY_GUARD_PROVIDER_PEER_PASS',findings=[],checks=count,guard=d(B/'check.py'),boundary=d(B/'boundary.json'),reviewer_source=d(Path(__file__)),reviewer_role='Authored the checked SourceRotation244 predecessor; independent reader of this new guard adaptation. New source mathematical peer belongs to another agent.',projects=9,tools=['Init'],probes=10,callers=13,inputs=inputs,scope='Full new guard delta and boundary read; unchanged runner/post/provider AST, selected current actual parent evidence checked. No new unit outcome or full ancestor review claimed.',supplied_execution=False)
(H/'review.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(checks=count,review=d(H/'review.json')),indent=2))
