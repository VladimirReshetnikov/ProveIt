import sys;sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,importlib.util,difflib
ROOT=Path('/home/codex/.codex/worktrees/9c9b/Proofs');OUT=Path('/tmp/gowers-next297-general-iteration-repair1-independent-review');SOURCE='9dce5ce380082bb050254e9625c6aa1ce48ae34a';REL='Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs18GeneralIteration.lean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def h(s):return hashlib.sha256(s.encode()).hexdigest()
a=subprocess.check_output(['git','show',SOURCE+':'+REL],cwd=ROOT).decode();b=(ROOT/REL).read_text();old='Q.isProper_of_step_pos (by decide)';new='Q.isProper_of_step_pos (by change 0 < (1 : Nat); decide)';assert a.count(old)==1 and a.replace(old,new)==b and len(a.splitlines())==len(b.splitlines())==66
parser=Path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py');assert sha(parser)=='8efad41a0a5f1ec5946154a0643920ce1f4bf47f25d1fd85de167cabe2448d1f';sp=importlib.util.spec_from_file_location('p',parser);p=importlib.util.module_from_spec(sp);sp.loader.exec_module(p);aa=p.declarations(a);bb=p.declarations(b);assert aa.keys()==bb.keys()and len(aa)==4;n='LeanProofs.GowersSzemeredi.hasNatAP_Icc_of_fin_interval';ledger=[]
for name,x in aa.items():
 y=bb[name];assert x['kind']==y['kind']and x['header']==y['header']and x['context']==y['context']and x['line']==y['line']
 if name!=n:assert x['block']==y['block']
 assert p.proof_lines(x)==p.proof_lines(y)
 ledger.append(dict(name=name,kind=x['kind'],header=x['header'],context=x['context'],line=x['line'],old_block_sha256=h(x['block']),new_block_sha256=h(y['block']),proof_lines_before=p.proof_lines(x),proof_lines_after=p.proof_lines(y)))
assert p.proof_lines(aa[n])==p.proof_lines(bb[n])==15 and p.imports(a)==p.imports(b)
receipt=Path('/tmp/gowers-next297-integrated9dce-core-attempt1/receipt.json');r=json.loads(receipt.read_text());log=Path(r['log']);assert r['source_commit']==SOURCE and r['status']=='failed'and type(r['terminal_exit'])is int and r['terminal_exit']==1 and sha(log)==r['log_sha256'];assert 'Expected type must not contain free variables' in log.read_text() and '0 < { start := 1, step := 1, length := N }.step' in log.read_text()
provider=ROOT/'Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs18NaturalIntervalIncrement.lean';definitions=ROOT/'Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean';assert 'theorem NatAP.isProper_of_step_pos (P : NatAP) (hstep : 0 < P.step) : P.IsProper := by' in provider.read_text()
invpath=ROOT/'Combinatorics/Ramsey/gowers-proof-status.json';inv=json.loads(invpath.read_text());occ=[]
def visit(v,path=[]):
 if isinstance(v,dict):
  if v.get('file')==REL:occ.append(dict(path=path,entry=v))
  for k,x in v.items():visit(x,path+[k])
 elif isinstance(v,list):
  for i,x in enumerate(v):visit(x,path+[i])
visit(inv);assert occ==[]
assert (ROOT/REL).read_text()==b
OUT.mkdir(exist_ok=False);(OUT/'before.lean').write_text(a);(OUT/'after.lean').write_text(b);(OUT/'changes.patch').write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+REL,tofile='b/'+REL)));(OUT/'interfaces.json').write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
report=dict(status='PASS independent narrow source repair review; targeted/native replay outcome not certified by this review',findings=[],failed_source_commit=SOURCE,owner=REL,original_source_sha256=h(a),repaired_source_sha256=h(b),exact_change=dict(before=old,after=new,occurrences=1,line=41),mathematics=['Q is the local NatAP structure ⟨1,1,N⟩, so its step projection is definitionally1 independently of N.','The existing provider asks only for0<Q.step. The change tactic exposes the definitionally equal closed proposition0<(1:Nat), and decide proves that proposition.','The properness proof therefore has the identical type and meaning. There is no added nonempty or positive-N hypothesis; N=0 and all original k/delta premises are preserved.'],preservation=dict(complete_declarations_headers_contexts=4,exact_non_theorem_blocks=1,other_complete_blocks_exact=3,changed_proof_body_lines_before=15,changed_proof_body_lines_after=15,owner_source_lines_before=66,owner_source_lines_after=66,source_delta=0,proof_delta=0,imports_identical=True,all_declaration_line_numbers_identical=True,inventory_owner_occurrences=occ,inventory_location_delta=[]),provider=dict(path=str(provider),sha256=sha(provider),line=11),definitions=dict(path=str(definitions),sha256=sha(definitions),NatAP_structure_line=63),preserved_failure=dict(receipt_path=str(receipt),receipt_sha256=sha(receipt),log_path=str(log),log_sha256=sha(log),terminal_exit=1,expected_core_modules=r['expected_modules'],diagnostic='Expected type must not contain free variables:0<{start:=1,step:=1,length:=N}.step'),inventory=dict(path=str(invpath),sha256=sha(invpath)),scope='Only one closed-goal elaboration clarification; preserves the approved source/proof saving and every public interface. No source import graph or validation root changes.',native_result_claimed=False,repository_git_cache_or_existing_evidence_modified=False,review_script=dict(path=str(Path(__file__)),sha256=sha(__file__)))
(OUT/'report.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');(OUT/'freeze.json').write_text(json.dumps({'assets':[{'path':str(p),'sha256':sha(p)}for p in sorted(OUT.iterdir())if p.is_file()]},indent=2)+'\n');print(json.dumps({'report_path':str(OUT/'report.json'),'report_sha256':sha(OUT/'report.json'),'freeze_sha256':sha(OUT/'freeze.json'),'repaired_source_sha256':h(b)},indent=2))
