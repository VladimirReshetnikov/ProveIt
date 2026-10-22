"""Peer controls on AST-extracted pure metadata guards only."""
from pathlib import Path
import ast,json,hashlib,tempfile
S=Path('/tmp/k215-phase11-publication');O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();f=json.loads((S/'freeze.json').read_text());assert sha(S/'freeze.json')=='6710724209e3bdbba299b44ef01723ea70b8cf30a2c15b85e0f8a33f44f0604c'
for n,r in f['files'].items():assert sha(S/n)==r['sha256']and(S/n).stat().st_size==r['bytes']
b=json.loads((S/'basis-reference.json').read_text());R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=R/b['repository_relative_directory']
for n,r in b['files'].items():assert sha(P/n)==r['sha256']and(P/n).stat().st_size==r['bytes']
t=ast.parse((S/'packet.py').read_text());node=next(n for n in ast.walk(t)if isinstance(n,ast.If)and"'report_axioms'"in ast.unparse(n.test))
checks=[]
def profile(ax,expect):
 env={'m':'Core','plans':{'Core':{'report_axioms':expect}},'reports':[('theorem'+str(i),a)for i,a in enumerate(ax)]};exec(compile(ast.Module(body=[node],type_ignores=[]),'held-profile-guard','exec'),env)
def ok(n,ax,exp):profile(ax,exp);checks.append({'name':n,'expected':'accept'})
def no(n,ax,exp):
 try:profile(ax,exp)
 except AssertionError:checks.append({'name':n,'expected':'reject'})
 else:raise AssertionError(n)
ok('three_empty_generic',['','',''],[[],[],[]]);ok('numeric_two_axioms',['propext, Quot.sound'],[['propext','Quot.sound']]);ok('order_inside_one_set_immaterial',['Quot.sound, propext'],[['propext','Quot.sound']])
no('generic_choice_rejected',['Classical.choice'],[[]]);no('generic_standard_axiom_rejected',['propext'],[[]]);no('numeric_missing_axiom_rejected',['propext'],[['propext','Quot.sound']]);no('numeric_extra_choice_rejected',['propext,Quot.sound,Classical.choice'],[['propext','Quot.sound']]);no('report_order_preserved',['propext',''],[[],['propext']]);no('missing_report_rejected',[],[[]]);no('extra_report_rejected',['',''],[[]])
res={'status':'PASS_METADATA_CONTROLS','positive':3,'negative':7,'checks':checks,'freeze_sha256':sha(S/'freeze.json'),'validator_sha256':sha(S/'packet.py'),'reviewed_current_files':len(f['files']),'rehashed_phase10_reference_files':len(b['files']),'compiler_or_producer_calls':0,'archive_or_live_capture_calls':0,'scope':'Exact profile conditional extracted from final held AST; no whole helper import, predecessor reader or archived code execution.'};(O/'controls.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
