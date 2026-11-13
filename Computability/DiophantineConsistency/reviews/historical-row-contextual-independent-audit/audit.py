#!/usr/bin/env python3
"""Static verification of independently captured contextual row output."""
import ast,hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent;REV=ROOT/'Computability/DiophantineConsistency/reviews';P=REV/'historical-row-contextual-audit';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('README.md','CHECK.json','terminal-observation.json','contextual-chain.py','controls.py','row-output.json'):
 p=P/name;rel=p.relative_to(ROOT).as_posix();old=subprocess.run(['git','show','fe3084dd85:'+rel],cwd=ROOT,capture_output=True,check=True).stdout
 if old!=p.read_bytes():raise ValueError(('committed packet drift',name))
assert H(P/'contextual-chain.py')=='470eb6dcbb05e66f303c7ee05350f46d884cd2f93eca3b1ff54bbfb588dcf163'
assert H(HERE/'row-output.json')==H(P/'row-output.json')==H(REV/'compact44-row-match-independent-audit/CHECK.json')=='db7690d62441f036f8275f5270416b015c8e0b2cc858de8b48ea19a703755df7'
tree=ast.parse((P/'contextual-chain.py').read_text());assign={}
for n in tree.body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('TARGETS','EDGES'):
  assign[n.targets[0].id]=ast.literal_eval(n.value)
assert assign['EDGES']=={'row':{'lookup'},'lookup':{'relabel','permutation'},'relabel':{'endpoint'},'permutation':{'endpoint'},'endpoint':set()}
assert set(assign['TARGETS'])==set(assign['EDGES'])
for target,(directory,digest) in assign['TARGETS'].items():assert H(REV/directory/'audit.py')==digest,(target,directory)
modified=[]
for n in ast.walk(tree):
 if isinstance(n,ast.Assign):
  for t in n.targets:
   if isinstance(t,ast.Attribute) and isinstance(t.value,ast.Name) and t.value.id=='m':modified.append(t.attr)
assert sorted(modified)==['PARENTAUDIT','subprocess'],modified
obs=json.loads((P/'terminal-observation.json').read_bytes());assert obs['packaged_guarded_exit']==0 and obs['hardened_exit']==0 and obs['lean_launched'] is False and obs['check_sha256']==H(P/'CHECK.json')
print(json.dumps({'status':'PASS_INDEPENDENT_CONTEXTUAL_ROW_EVIDENCE','reviewed_commit':'fe3084dd85','independent_view_preparation_session':39193,'independent_view_preparation_exit':0,'independent_contextual_session':88042,'independent_contextual_exit':0,'independent_controls_exit':0,'row_stdout_sha256':H(HERE/'row-output.json'),'targets_checked':sorted(assign['TARGETS']),'original_module_global_overrides':sorted(modified),'scope':'Whitelisted audit subprocess rerouting and endpoint historical plan-path rebound only; not an unchanged live-chain audit pass, current-source validation, Lean build or iPRA theorem.'},indent=2))
