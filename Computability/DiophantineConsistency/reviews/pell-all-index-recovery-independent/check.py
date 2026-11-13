#!/usr/bin/env python3
"""Audit noncircular all-index Pell folding and recovery without Lean."""
import ast,json,os,re,sys
from hashlib import sha256
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];B=D/'research';PRIOR=B/'ordinary12-direct90-ipra-join/observations/attempt03/result.json';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
ENTRIES=[
 ('pell-all-index-fold-prototype','PellFold','attempt02','d1c55d280615310987f55d68717a671e9ce3cd917bd83697da25129d05388d34','302aefad9e2d7a9b4fce22e989d4c4a791f3e79ef83cb6f245a2ed0ed1b4140e','df1799b158b3b7992b3c76e11b162cacbeced96a650fcbf425a5709c2f490382'),
 ('pell-all-index-odd-fold-prototype','PellOddFold','attempt02','5ecd8b100a2bbc9ede5d015ef25de80a0c3f887fefa7e04480c23b0ccde94ad2','853721216a20dbf04c1babafbbb79526d92db0aee5f3a6127625d86208bc3175','6c84bcc311835e56f24d82897ae66d91baa519804b9931112bcaeb10f9edf2e2'),
 ('pell-all-index-recovery-prototype','PellRecovery','attempt01','8c9c824476b9bfc2431a421b2e8a9a405198ee88ff5e6f3f9b55e7268a385c47','0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a','1f230d0509d3833bee147eb98d69463462bdc08fbd6906edba18e3cb7918be8e'),
 ('ten-positive-80-folding-complete-prototype','Direct80Fold','attempt03','56b27821ec3f7f0d4e64f923b1133118db54f742427ceb15533447be08217ae2','40c76ff3acfa34f04930608ae981619c5a958ad8d280945a2b64f877906d8571','4c61c70c45dcf0a194c43bdcfd2151f8840685408e40e786f19b06acd9bd0dd1')]
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
need(sha(PRIOR)=='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed','prior 90 receipt')
old=json.loads(PRIOR.read_text());need(old['status']=='PASS','prior join');inputs={};direct={};outputs={};samples=0
for directory,module,attempt,source_pin,obj_pin,terminal_pin in ENTRIES:
 root=B/directory;source=root/(module+'.lean');runner=root/'run.py';obs=root/'observations'/attempt;t=obs/'terminal.json'
 need(sha(source)==source_pin and sha(t)==terminal_pin,'source/terminal pin '+module)
 r=json.loads(t.read_text());pins=r['pins'];need(r['exit']==0 and r['reason'] is None and pins==r['after'],'author status '+module)
 need(sha(obs/'source.txt')==pins['source']==source_pin and sha(runner)==pins['runner'] and sha(LEAN)==pins['lean'],'source/runner/tool '+module)
 obj=Path(r['output_root'])/(module+'.olean');need(sha(obj)==r['object_sha256']==obj_pin,'object '+module);outputs[module]=obj_pin
 need(sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256'] and not (obs/'stderr').read_bytes(),'logs '+module)
 text=(obs/'stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',text) and 'sorryAx' not in text,'diagnostic '+module)
 reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
 need(reports and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axiom reports '+module)
 pre=r['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
 for x in r['samples']:
  need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2,'resource sample');samples+=1
 provider=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean')
 need(sha(provider)==pins['direct_provider'],'direct provider '+module)
 tree=ast.parse(runner.read_text());assign=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='extra' for t in n.targets))
 extras=[Path(ast.literal_eval(x.args[0])) for x in assign.value.elts];need([sha(x) for x in extras]==pins['extra'],'predecessor pins '+module)
 roots=[Path(x) for x in r['lean_path'].split(':')]
 for name in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
  rel=Path(name.replace('.','/')+'.olean');selected=next((p/rel for p in roots if (p/rel).is_file()),None);need(selected is not None,'missing direct import '+name)
  if '.' in name:
   ns=next((p for p in roots if (p/name.split('.')[0]).is_dir()),None);need(ns is not None and (ns/rel).is_file(),'namespace shadow '+name)
  direct[name]={'path':str(selected),'sha256':sha(selected)};prior=old['post_headers']['project'].get(name)
  if prior:
   need(direct[name]['sha256']==prior['record']['sha256'],'prior direct import '+name);stem=str(selected)[:-len('.olean')]
   for suffix,v in prior['companions'].items():
    now=rec(stem+suffix);need((None if now is None else now['sha256'])==(None if v is None else v['sha256']),'prior companion '+name+suffix)
 inputs[str(source)]=source_pin;inputs[str(t)]=terminal_pin;inputs[str(obj)]=obj_pin
for directory,pin in [('pell-all-index-fold-prototype','58943def5a4584166d513ee7993ed3a7e65234f6bf62f7b99b797d8dced9673c'),('pell-all-index-odd-fold-prototype','c570e9499774b89558b9d86a520d02c3add8b41b608463c9c7c2e2df10c75250')]:
 obs=B/directory/'observations/attempt01';t=obs/'terminal.json';need(sha(t)==pin,'failed receipt pin');inputs[str(t)]=pin
 r=json.loads(t.read_text());need(r['exit']!=0 and sha(obs/'source.txt')==r['pins']['source'] and sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256'] and 'error' in (obs/'stdout').read_text()+(obs/'stderr').read_text(),'failed attempt')
for attempt,pin in [('attempt01','da863475ce9dd2ac3745cdea470b9c8c3ca4c95038cbc799af77c6af3c9f2f0f'),('attempt02','009e1bbf6012d9248d2e1e6ac83c1e592cef08cd290f5ebad55ae270cc5f0c99')]:
 obs=B/'ten-positive-80-folding-complete-prototype/observations'/attempt;t=obs/'terminal.json';need(sha(t)==pin,'graph failed receipt');inputs[str(t)]=pin
 r=json.loads(t.read_text());need(r['exit']!=0 and sha(obs/'source.txt')==r['pins']['source'] and sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256'] and 'error' in (obs/'stdout').read_text()+(obs/'stderr').read_text(),'graph failed attempt')
fold=(B/ENTRIES[0][0]/'PellFold.lean').read_text();odd=(B/ENTRIES[1][0]/'PellOddFold.lean').read_text();recovery=(B/ENTRIES[2][0]/'PellRecovery.lean').read_text()
need('induction k using ISigma1.sigma1_succ_induction' in fold and 'theorem y_reflected_mod' in fold,'arbitrary block/reflection')
need('(hn : 0<n) (hs : s%2=1)' in odd and 's%(2*n)' in odd and '∃ p : V, p≤n ∧ p%2=1' in odd,'odd fold assumptions')
need(all(x in recovery for x in ('(hn : 0<n) (hs : s%2=1)','(hc : 0<c) (hci : c<ycoord n b)',
 '(hsize : 2*ycoord n b<xcoord n b)','SignMod (xcoord n b) c (ycoord s b)',
 '∃ p : V, 0<p ∧ p<n ∧ p%2=1 ∧ c=ycoord p b')),'recovery assumptions/conclusion')
for text in (fold,odd,recovery):need(not re.search(r'\bhalf_index\b|\bhmain\b',text),'half_index/main norm invocation')
# Direct80Joined is imported transitively by PellFold; the prior independent
# packet verifies its strong norm is derived and it does not invoke half_index.
joined_path=B/'ten-positive-80-folding-joined-prototype/Direct80Joined.lean'
need(sha(joined_path)=='e18f08d8090b79ffb53695ee3e35a1b9002d088e8110f3e06518d7179929dc50','joined source pin')
inputs[str(joined_path)]=sha(joined_path);joined=joined_path.read_text()
need(not re.search(r'\bhalf_index\b|\bhmain\b',joined) and 'graph_adjacent p v hb hv hz' in joined,'joined source noncircularity')
consequence=B/'ten-positive-80-folding-consequences-prototype/Direct80Consequences.lean'
need(sha(consequence)=='18586777cbbb54a6baca648f6cc890425bca9978578aa72a725f773c4f9fa3ab','consequence source pin')
cs=consequence.read_text(); graph=(B/ENTRIES[3][0]/'Direct80Fold.lean').read_text()
need(not re.search(r'\bhalf_index\b|\bhmain\b',cs+graph),'graph chain noncircular')
need(all(x in graph for x in ('(hb : 0<(p 0:V)) (hv : ∀j,0<v j)', '(hz : InternalZero (graph (integerPorts p)).output v)', 'c p v=ycoord r (A p v-1)', 'c p v*c p v∣I', 'signed_coordinate p v hb hv hz', 'recover_odd_ordinate j (2*h+1) (A0-1) C hj hsodd hC', 'have hD4 : 4≤D', 'have hCIstrict : C<I', 'have hFsize : 2*I<F', 'have h := norm j (A0-1)')), 'graph theorem and recovery witnesses')
need('strong_and_auxiliary_indices_with_graph_residue p v hb hv hz' in cs and 'sign_trans hF (sign_symm hgc) hgu' in cs,'same strong/auxiliary witness')
inputs[str(consequence)]=sha(consequence)
for path,digest in inputs.items():need(sha(path)==digest,'input changed '+path)
for name,row in direct.items():need(sha(row['path'])==row['sha256'],'direct import changed '+name)
print(json.dumps({'status':'PASS','accepted_modules':outputs,'direct_imports':direct,'prior_failures':4,'resource_samples':samples,
 'half_index_invoked_in_checked_sources':False,'scope':'abstract and graph-specific internal-index folding/recovery source and receipt audit; no Lean replay, graph-to-halt conclusion, or full historical ancestry'},indent=2,sort_keys=True))
