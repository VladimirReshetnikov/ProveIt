#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-named-prefix-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-named-prefix-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='993318f7e7d541abbeac89c01580ac7e82e06ed41d9f8bb390e89b4591e411c6' and sha(A/'outer-terminal-author-record.json')=='88df8b108edf7811d3f6e4785fd67d8c548f934b7fc5f17a02f644882c833243';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(76932,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1059 and s['runner_sha256']==sha(P/'run.py')=='792eec9d7ef1ae4675c04b9bbc002a59592c4a8d493dd1260b8ae6229304e576';r=s['rows'][0];n='Sign33MacroPrefixes';assert r['module']==n and r['source_sha256']=='0d78f54214e3c0a2a83dce4062385ec050494f288797bb02cb59ac2cd6a0af8d'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='418296ec903c9f956e982ea1126a2ce8e92cbfed70c7095b0af782dc8d8b3516'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
v=r['dependencies']['DiophantineConsistency.Sign33MacroRecipe'];assert v['sha256']=='ad746dde4c868da21963986e3255688d531ef7bed07d16a16970ac4819433045' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='de4ca919a103d330062bad991a9d087d8c693ab5cf5a32545fd519557600bcc8' and "'DiophantineConsistency.Sign33MacroPrefixes.recipe_eq_named' does not depend on any axioms" in log and 'warning:' not in log
review=D/'reviews/nine-seed33-jones-named-prefix-prelaunch-frontier-independent/check.py';assert sha(review)=='f13e6276d733bb064cacc9747a67d0818f814e3ccf5b0809227f1282eeae5991';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':76932,'guard_slots':100,'overlay_links':1059,'scope':'Lean recipe equals named prefix d45, axiom-free; no evaluator equality or JSON/human binding'},indent=2,sort_keys=True))
