from pathlib import Path
import ast,collections,hashlib,json,re,subprocess,sys,tempfile,shutil
D=Path(__file__).resolve().parents[2];h=D/'research/trace75-upstream-ten-runner-triage';o=h/'observations/attempt03';ctl=h/'observations/parser-policy-attempt02'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
assert sha(h/'check.py')==sha(o/'source.txt')=='4221feae3c636a5b6f33a469c7f3116ccb8158e799424ce37bd03f389cf11e85';assert sha(o/'terminal.json')=='54b54364f4e6521ee0d5e471bde24d0bd8dfab7b4bb8839a34d9708577d79ed0' and sha(o/'stdout')=='d31977de4a6c5c724f52c9b43a1caeb173a2a979a5834ab8c68b87ee4aa3a7be';assert sha(ctl/'terminal.json')=='3ddba4a4bd319e3c44149d9599685a2de609353a134855820ee9cbfc82ff69bc'
for q in (o,ctl):
 t=load(q/'terminal.json');assert t['exit']==0 and t['checker_sha256']==sha(h/'check.py') and t['stdout_sha256']==sha(q/'stdout') and t['stderr_sha256']==sha(q/'stderr')
t=load(ctl/'terminal.json');assert t['control_sha256']==sha(h/'test-parser.py')==sha(ctl/'source.txt');c=load(ctl/'stdout');assert c['status']=='PASS' and len(c['tests'])==8 and all(c['tests'].values())
with tempfile.TemporaryDirectory() as x:
 p=Path(x);[shutil.copyfile(h/f,p/f) for f in ('check.py','test-parser.py')];z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'test-parser.py')],capture_output=True,text=True);assert z.returncode==0 and all(json.loads(z.stdout)['tests'].values())
inv=D/'research/trace75-upstream-141-inventory/observations/attempt01/stdout';fin=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json';assert sha(inv)=='87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575' and sha(fin)=='b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'
final=load(fin);inventory=load(inv);result=load(o/'stdout');records={r['module']:r for r in result['records']};assert len(records)==10

def evaluate(n,env):
 if isinstance(n,ast.Constant) and isinstance(n.value,str):return n.value
 if isinstance(n,ast.Name):return env[n.id]
 if isinstance(n,ast.List):return [evaluate(x,env) for x in n.elts]
 if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='Path' and len(n.args)==1 and not n.keywords:return Path(evaluate(n.args[0],env))
 if isinstance(n,ast.BinOp):
  a=evaluate(n.left,env);b=evaluate(n.right,env)
  if isinstance(n.op,ast.Add):return a+b
  if isinstance(n.op,ast.Div):return a/b
 if isinstance(n,ast.ListComp) and len(n.generators)==1:
  g=n.generators[0];assert isinstance(g.target,ast.Name) and not g.ifs and not g.is_async;return [evaluate(n.elt,{**env,g.target.id:v}) for v in evaluate(g.iter,env)]
 raise AssertionError(ast.dump(n))
def static_paths(path):
 tree=ast.parse(path.read_text());env={};seq=None;captured=False;parents={c:n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
 for node in ast.walk(tree):
  if (isinstance(node,ast.Subscript) and isinstance(node.value,ast.Name) and node.value.id=='extra' and isinstance(node.ctx,(ast.Store,ast.Del))) or (isinstance(node,ast.Name) and node.id=='extra' and isinstance(node.ctx,(ast.Store,ast.Del))) or (isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and isinstance(node.func.value,ast.Name) and node.func.value.id=='extra'):
   cur=node
   while cur in parents and not isinstance(parents[cur],ast.Module):cur=parents[cur]
   assert isinstance(cur,(ast.Assign,ast.AugAssign,ast.Expr)) and cur in tree.body,(path,node.lineno)
 for node in tree.body:
  if isinstance(node,ast.Assign):
   for t in node.targets:
    if isinstance(t,ast.Name) and t.id=='lib':env['lib']=evaluate(node.value,env)
    if isinstance(t,ast.Name) and t.id=='extra':assert seq is None and not captured;seq=evaluate(node.value,env)
    if isinstance(t,ast.Name) and t.id=='pins':captured=True
  elif isinstance(node,ast.AugAssign) and isinstance(node.target,ast.Name) and node.target.id=='extra':assert not captured and isinstance(node.op,ast.Add);seq.extend(evaluate(node.value,env))
  elif isinstance(node,ast.Expr) and isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Attribute) and isinstance(node.value.func.value,ast.Name) and node.value.func.value.id=='extra':
   call=node.value;assert not captured and len(call.args)==1 and not call.keywords;v=evaluate(call.args[0],env)
   if call.func.attr=='append':seq.append(v)
   elif call.func.attr=='extend':seq.extend(v)
   else:raise AssertionError(call.func.attr)
 assert captured and isinstance(seq,list);return seq

def first(n,roots):
 parts=n.split('.')
 for root in roots:
  p=root/('/'.join(parts)+'.olean')
  if len(parts)>1 and (root/parts[0]).is_dir():return p if p.is_file() else None
  if p.is_file():return p
 return None
project=final['selected_project'];outside=final['selected_outside'];expected={}
for x in inventory['records']:
 if x['module']=='ScaledOffsetGeneric' or x['exact_producer_in_six_runs'] or not x['prior_capture'] or not x['prior_capture']['all_companions_match'] or not x['prior_candidate_receipts']:continue
 projectimports={n for n in x['selected_header'] if n in project};compared={e['module'] for r in x['prior_candidate_receipts'] for e in r['recorded_direct_comparisons'] if e.get('matches')}
 if not projectimports<=compared:expected[x['module']]=x
assert set(expected)==set(records)
counts=collections.Counter()
for n,x in expected.items():
 row=records[n];assert len(x['prior_candidate_receipts'])==1;candidate=x['prior_candidate_receipts'][0];rp=Path(candidate['path']);assert sha(rp)==candidate['sha256']==row['receipt_sha256'] and str(rp)==row['receipt'];q=load(rp);assert q['exit']==0 and q['reason'] is None and q['pins']==q['after'];obj=Path(q['output_root'])/(n.replace('.','/')+'.olean');assert obj.is_file() and str(obj.resolve())==x['selected_realpath']==row['output_realpath'] and sha(obj)==q['object_sha256']==x['selected_olean_sha256']
 src=rp.parent/'source.txt';copy=Path(q['command'][5]);assert sha(src)==sha(copy)==q['pins']['source']==row['source_sha256'];imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);assert imports==[d for d in x['selected_header'] if d!='Init']
 for ext in ('stdout','stderr'):assert sha(rp.parent/ext)==q[ext+'_sha256']
 candidates=[p for p in rp.parents[2].glob('*.py') if p.is_file() and sha(p)==q['pins']['runner']];assert len(candidates)==1 and str(candidates[0])==row['runner'] and sha(candidates[0])==row['runner_sha256'];paths=static_paths(candidates[0]);assert len(paths)==len(q['pins']['extra'])==row['positional_pin_count'] and len(row['direct'])==len(imports)
 for dep,reported in zip(imports,row['direct']):
  now=first(dep,[Path(v) for v in q['lean_path'].split(':')]);chosen=project.get(dep) or outside.get(dep);assert now is not None and sha(now)==chosen['.olean']['sha256'];ix=[i for i,p in enumerate(paths) if p==now and sha(now)==q['pins']['extra'][i]];status='current_first_path_in_positional_pins' if ix else 'not_named_by_positional_path_list';assert reported=={'module':dep,'recorded_lean_path_current_first':str(now),'final_selected_realpath':chosen['.olean']['resolved'],'final_selected_sha256':chosen['.olean']['sha256'],'current_first_matches_final_hash':True,'positional_indexes':ix,'classification':status};counts[status]+=1
assert counts=={'current_first_path_in_positional_pins':17,'not_named_by_positional_path_list':1};assert records['CarrierSizes']['direct'][0]['classification']=='not_named_by_positional_path_list';print('PASS independent 10 receipts, AST paths with nested extra mutation scan, 17/18 named first selections and 8 copied parser controls')
