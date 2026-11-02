#!/usr/bin/env python3
"""Independent static, mutation, and toy review; no real paired run."""
import ast, copy, hashlib, importlib.util, json, re, shutil, subprocess, sys, tempfile
from pathlib import Path
if not __debug__: raise RuntimeError('review requires assertions enabled')
ROOT=Path(__file__).resolve().parents[4]
R=ROOT/'Computability/DiophantineConsistency/research'
T=R/'ipra-selected-native-bit'; H=T/'historical'; REVIEW=Path(__file__).resolve().parent
A=ROOT/'Computability/DiophantineConsistency/reviews/ipra-selected-native-bit-guarded-author'
AA=ROOT/'Computability/DiophantineConsistency/reviews/ipra-selected-native-bit-guarded-author-independent-audit'
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
names=('task-policy.json','prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py','run_controls.py','test_history.py','test_prepare.py','test_freeze.py','test_real_extension.py','test_full_chain.py','check_package_choice.py','test_package_choice.py','test_author_ancestry_gate.py','test_real_policy.py','REAL-RUN.md','policy-preflight.py','../paired_plan.py','../author-additions.json')
files=[(H/n).resolve() for n in names]
extra=[H/'provisional-plan.json',A/'state.json',AA/'receipt.json',AA/'terminal-observation.json',Path(__file__).resolve()]+sorted((A/'logs').glob('*.log'))
before={str(p):digest(p) for p in files+extra}
assert digest(H/'task-policy.json')=='70923d446875a9a99eb02d4315264cc0eb66837b79e5ace66b9fc12e2313dde9'
assert digest(T/'author-additions.json')=='7eb9d405153d4de522b3b10007003691de860565a882c1f83e8cd3d589bb2607'
assert digest(A/'state.json')=='3bee2db67ca881cf02458d6688f3b8252eab6cc36ce2b7a610d2ef2a84127321'
assert digest(AA/'receipt.json')=='e47a76773c98a19ffdf90165ffda5b2f338c9b03bb31f92cc7aa8403656c8516'
assert digest(AA/'terminal-observation.json')=='ab4a876dc8e60b13f55f9b4ee43b3e3fdd29bd8a8871265e4a13d6671e1d37b9'
p=json.loads((H/'task-policy.json').read_text()); m=json.loads((T/'author-additions.json').read_text()); state=json.loads((A/'state.json').read_text())
audit=json.loads((AA/'receipt.json').read_text()); terminal=json.loads((AA/'terminal-observation.json').read_text())
assert terminal['observed_exit_code']==0 and terminal['receipt_sha256']==digest(AA/'receipt.json')
assert audit['status']=='PASS_INDEPENDENT_SELECTED_NATIVE_BIT_AUTHOR_ARTIFACT_AUDIT' and audit['added_modules']==11 and audit['added_direct_import_edges']==37
assert len(m['order'])==11 and p['addition_order']==m['order']==[r['module'] for r in state['rows']] and p['target']==m['order'][-1]
assert len(set(m['order']))==11 and sum(len(row['imports']) for row in state['rows'])==37
choices={'DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral','DiophantineConsistency.IPRASquareSumsNative'}
for name in m['order']:
 author=m['sources'][name]; chosen=p['sources'][name]; expected=author.copy()
 if name in choices: expected['workspace_path']='Computability/DiophantineConsistency/Lean/'+name.replace('.','/')+'.lean'
 assert chosen==expected
 draft=git('show',m['source_commit']+':'+author['workspace_path'])
 assert hashlib.sha256(draft).hexdigest()==author['sha256']
 path=chosen['workspace_path']; assert git('ls-files','--error-unmatch','--',path).decode().strip()==path
 subprocess.run(['git','diff','--quiet','HEAD','--',path],cwd=ROOT,check=True)
 assert git('show','HEAD:'+path)==(ROOT/path).read_bytes()==draft
assert set(p['sources'])==set(m['order'])
expected={n:m['axiom_reports'].get(n,[]) for n in m['order']}
assert p['expected_axiom_by_module']==expected and p['expected_axiom_names']==expected[p['target']]
freeze_tree=ast.parse((H/'freeze.py').read_text())
freeze_expected=[node.value for node in freeze_tree.body if isinstance(node,ast.Assign) and any(isinstance(target,ast.Name) and target.id=='EXPECTED' for target in node.targets)]
assert len(freeze_expected)==1 and list(ast.literal_eval(freeze_expected[0]))==p['expected_axiom_names'], 'freezer target diagnostic constants do not match task policy'
assert sorted(map(len,expected.values()))==[0,0,0,0,0,0,1,2,2,5,8]
pattern=re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",re.M)
for i,row in enumerate(state['rows']):
 logs=list((A/'logs').glob(f'{i:03d}-*.log')); assert len(logs)==1 and digest(logs[0])==row['log_sha256'] and row['exit']==0
 reports=pattern.findall(logs[0].read_text()); assert [n for n,_ in reports]==expected[row['module']] and [list(x) for x in reports]==row['axiom_reports']
 for _,axioms in reports: assert set(filter(None,re.split(r'\s*,\s*',axioms.strip()))) <= {'propext','Classical.choice','Quot.sound'}
plan=json.loads((H/'provisional-plan.json').read_text())
assert plan['status']=='PROVISIONAL_MANIFEST_PLAN' and len(plan['parent_source_modules_used'])==1096 and plan['additional_project_modules']==m['order']
assert plan['parent_source_drift'] is None and plan['parent_manifest_sha256']=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
# Compare generic replay drivers to the previously audited selected-checker revision, not merely the mutable worktree.
for name in ('rebuild.py','compare.py','run_pair.py'):
 ref='Computability/DiophantineConsistency/research/ipra-selected-refutation-verifier/historical/'+name
 assert git('show','c8b07a001b:'+ref)==(H/name).read_bytes()
ref=git('show','c8b07a001b:Computability/DiophantineConsistency/research/ipra-selected-refutation-verifier/historical/prepare.py').decode()
current=(H/'prepare.py').read_text()
ref=re.sub(r"^POLICY_(?:REL|SHA256) = .*$",'',ref,flags=re.M)
current=re.sub(r"^POLICY_(?:REL|SHA256) = .*$",'',current,flags=re.M)
assert ref==current
# Explicitly exercise the unchanged planner's shadow refusal using an isolated toy tree.
spec=importlib.util.spec_from_file_location('frontier13_plan',T/'paired_plan.py'); mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
with tempfile.TemporaryDirectory(prefix='independent-shadow-') as tmp:
 q=Path(tmp); live=q/'lib/Toy/A.lean'; draft=q/'draft/A.lean';live.parent.mkdir(parents=True);draft.parent.mkdir(parents=True);live.write_text('-- live\n');draft.write_text('-- draft\n')
 try: mod.plan(q,q,{'status':'FROZEN_NOT_COMPILED','sources':{},'order':[],'project_modules':0},{'Toy':q/'lib'},['Toy.A'],{'Toy.A':draft},'historical')
 except ValueError as e: assert 'draft shadows live source' in str(e)
 else: raise AssertionError('draft shadow was accepted')
 assert live.read_text()=='-- live\n' and draft.read_text()=='-- draft\n'
# Inspect the actual runbook and directly execute its author ancestry gate under mutations.
shell=(H/'REAL-RUN.md').read_text().split('```bash\n',1)[1].split('\n```',1)[0]
r=subprocess.run(['bash','-n'],input=shell,text=True,capture_output=True);assert r.returncode==0,r.stderr
bodies=re.findall(r"python3 - <<'([^']+)'\n(.*?)\n\1(?:\n|$)",shell,re.S);assert len(bodies)==5
nodes=[]
for _,body in bodies:
 tree=ast.parse(body);nodes += [x for x in ast.walk(tree) if isinstance(x,ast.If) and 'added_direct_import_edges' in ast.unparse(x.test)]
assert len(nodes)==1
code=compile(ast.fix_missing_locations(ast.Module(body=nodes,type_ignores=[])),'actual-author-gate','exec')
def accepts(a):
 try: exec(code,{'author':a,'ValueError':ValueError})
 except ValueError: return False
 return True
assert accepts(audit)
for n in (35,36,38):
 x=copy.deepcopy(audit);x['added_direct_import_edges']=n;assert not accepts(x)
for required in ('PASS_INDEPENDENT_SELECTED_NATIVE_BIT_WORKFLOW_REVIEW','observed_exit_code','receipt_sha256','workspace_head_before','workspace_head_after','preparer-process.json','freezer-process.json','pair-observation.json','--expected-axiom-reports', 'MATCHED_SELECTIVE_PASS 11 affected modules'):
 assert required in shell or required in (H/'REAL-RUN.md').read_text()
# Run published package and ancestry tests independently, with actual captured exits.
results=[]
def run(cmd,cwd=None):
 r=subprocess.run([str(x) for x in cmd],cwd=cwd,text=True,capture_output=True,timeout=360)
 results.append({'command':[str(x) for x in cmd],'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr});return r
for name in ('check_package_choice.py','test_package_choice.py','test_author_ancestry_gate.py','test_real_policy.py'):
 assert run([sys.executable,H/name]).returncode==0
 assert run([sys.executable,'-O',H/name]).returncode!=0
# Copy fixtures away from the reviewed tree: run_controls refuses receipt overwrites.
with tempfile.TemporaryDirectory(prefix='independent-frontier13-controls-') as tmp:
 research=Path(tmp)/'Computability/DiophantineConsistency/research';h=research/'ipra-selected-native-bit/historical';h.mkdir(parents=True)
 for f in H.glob('*.py'): shutil.copy2(f,h/f.name)
 shutil.copy2(H/'task-policy.json',h/'task-policy.json')
 for f in ('paired_plan.py','author-additions.json'): shutil.copy2(T/f,h.parent/f)
 dest=research/'fresh-project-closure';dest.mkdir()
 for f in ('rebuild.py','compare.py','run_pair.py'): shutil.copy2(R/'fresh-project-closure'/f,dest/f)
 outcome=run([sys.executable,h/'run_controls.py'],h);assert outcome.returncode==0,(outcome.stdout,outcome.stderr)
 control=json.loads((h/'control-receipt.json').read_text());assert control['status']=='PASS_HISTORICAL_TOY_CONTROLS' and len(control['controls'])==12
 assert all(row['exit_code']==0 for row in control['controls'][:6]) and all(row['exit_code']!=0 for row in control['controls'][6:])
 controls=[{'script':Path(row['script']).name,'mode':row.get('mode','normal'),'exit_code':row['exit_code'],'stdout':row['stdout'],'stderr':row['stderr']} for row in control['controls']]
assert before=={str(p):digest(p) for p in files+extra}
out={'status':'PASS_INDEPENDENT_SELECTED_NATIVE_BIT_WORKFLOW_REVIEW','modules':11,'reports':18,'report_split':[8,5,2,1,2], 'author_direct_imports':37,'provisional_parent_rows':1096,'required_full_parent_rows':1210,'inputs_sha256':{str(p):before[str(p)] for p in files},'additional_inputs_sha256':{str(p):before[str(p)] for p in extra},'commands':results,'toy_controls':controls,'scope':'Static and toy review only; no real selected-native-bit paired replay. Historical parent, package-transitive, dynamic-load, transient-mutation, Foundation wrapper outer exit, and PDF transcription limitations remain.'}
receipt=REVIEW/'receipt.json'
if receipt.exists() or receipt.is_symlink():raise ValueError('refusing receipt overwrite')
receipt.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('PASS_INDEPENDENT_SELECTED_NATIVE_BIT_WORKFLOW_REVIEW',digest(receipt),flush=True)
