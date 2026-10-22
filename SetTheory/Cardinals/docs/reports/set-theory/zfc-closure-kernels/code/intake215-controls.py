#!/usr/bin/env python3
# SPDX-License-Identifier: MIT-0
"""Own bounded metadata controls; executes only the own recovery helper."""
from pathlib import Path
import copy,hashlib,json,subprocess,sys,tempfile,importlib.util
B=Path(__file__).resolve().parent
base=json.loads((B/'intake215-placement.json').read_text());records=[]
cases=[]
x=copy.deepcopy(base);x['archives'][0]['archive_sha256']='0'*64;cases.append(('wrong_archive_identity',x))
x=copy.deepcopy(base);next(r for r in x['members'] if r['route']=='git')['sha256']='0'*64;cases.append(('wrong_git_alias_digest',x))
x=copy.deepcopy(base);r=next(r for r in x['members'] if r['route']=='delivery_member');r['target_manuscript']=99;cases.append(('forward_delivery_alias',x))
x=copy.deepcopy(base);x['members'].pop();cases.append(('missing_member',x))
with tempfile.TemporaryDirectory(prefix='intake215-controls-') as d:
 for name,mutant in cases:
  p=Path(d)/(name+'.json');p.write_text(json.dumps(mutant))
  argv=[sys.executable,str(B/'recover.py'),'--repo','/home/codex/.codex/worktrees/ec20/Proofs','--map',str(p),'--planned-copy-map',str(B/'payload-copy-map.json'),'--verify-only']
  r=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
  assert r.returncode!=0,(name,r.stdout,r.stderr)
  records.append({'name':name,'exit_code':r.returncode,'error':r.stderr.strip().splitlines()[-1],'mutation':'All unmentioned JSON fields retain the exact original map','mutant_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
result={'status':'PASS_FOUR_NEGATIVE_METADATA_CONTROLS','helper_sha256':hashlib.sha256((B/'recover.py').read_bytes()).hexdigest(),'map_sha256':hashlib.sha256((B/'intake215-placement.json').read_bytes()).hexdigest(),'control_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'positive_record_sha256':hashlib.sha256((B/'recovery-plan.json').read_bytes()).hexdigest(),'cases':records,'supplied_code_or_compiler_executed':False,'canonical_changes':False}
(B/'controls-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
