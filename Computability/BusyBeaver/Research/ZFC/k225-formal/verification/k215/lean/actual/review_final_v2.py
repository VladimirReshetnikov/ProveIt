#!/usr/bin/env python3
"""Read-only final binding audit of the fresh Lean closure and explicit endpoint clients."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inv=json.loads((P/'inventory-v3.json').read_text());entries={r['module']:r for r in inv['project_modules']}
done=json.loads((P/'completed.json').read_text());attempts=json.loads((P/'attempts.json').read_text());completion=json.loads((P/'build-complete.json').read_text())
assert len(entries)==204 and set(done)==set(entries)
assert completion['completed_sha256']==sha(P/'completed.json')
assert inv['direct_external_imports']==['Init']
seen=set();warnings={};objects={};edges={};seconds=0
for e in inv['project_modules']:
 m=e['module'];r=done[m];source=ROOT/e['relative_source'];deps=set(e['imports'])&entries.keys();assert deps<=seen,m
 assert r['dependencies']=={d:done[d]['object_sha256'] for d in deps},m
 assert sha(source)==e['sha256']==r['source_sha256'],m
 assert r['status']=='PASS' and r['exit_code']==0 and not r['timed_out'],m
 assert r['source_unchanged'] and r['companions'],m
 for f,h in r['companions'].items():assert sha(f)==h,f
 log=Path(r['log']);assert sha(log)==r['log_sha256'],m
 text=log.read_text();assert ': error:' not in text and 'error: ' not in text,m
 warnings[m]=len(re.findall(r'\bwarning:',text));seconds+=r['seconds'];objects[m]=r['object_sha256'];edges[m]=sorted(deps);seen.add(m)
assert len(attempts)==len(done)+2
failures=[r for r in attempts if r['status']!='PASS'];assert len(failures)==2
assert failures[1]['module']=='BusyBeaver.ZFC.DomRho8' and failures[1]['index']==199 and not failures[1]['timed_out']
assert failures[1]['exit_code']==1 and 'Application type mismatch' in Path(failures[1]['log']).read_text()
assert failures[0]['module']=='BusyBeaver.ZFC.KSource215' and failures[0]['timed_out']
assert Path(failures[0]['log']).read_bytes()==b''
audits={}
for label,expected in [('independent',2),('axiom-components',8)]:
 folder=P/'audit'/label;r=json.loads((folder/'verification.json').read_text());assert r['status']=='PASS' and r['inputs_unchanged'] and not r['timed_out']
 assert r['exact_module_set'] and r['exact_direct_dependency_edges'] and r['modules']==204
 assert r['before']==r['after']
 for f,h in r['after'].items():assert sha(f)==h,f
 for f,h in r['fresh_companions'].items():assert sha(f)==h,f
 log=folder/'compiler.log';assert sha(log)==r['log_sha256']
 text=log.read_text();reports=re.findall(r"([^\n]+) depends on axioms: \[([^\]]*)\]",text,re.S)
 # Lean wraps axiom lists, but declaration headers remain on a single line.
 no_axioms=re.findall(r'([^\n]+) does not depend on any axioms',text)
 assert len(reports)+len(no_axioms)==expected,(label,text)
 symbols={x.strip() for _,body in reports for x in body.split(',') if x.strip()}
 assert symbols<={'propext','Classical.choice','Quot.sound'},symbols
 assert 'sorryAx' not in text
 audits[label]={'record_sha256':sha(folder/'verification.json'),'log_sha256':sha(log),'reports':expected,'axioms':sorted(symbols),'warnings':len(re.findall(r'\bwarning:',text)),'seconds':r['seconds'],'source_sha256':r['source_sha256'],'objects':r['fresh_companions']}
result={'status':'PASS','scope':'Exact fresh current-source project dependency closure and two closed typed endpoint audits; no Rocq result inferred.','target':inv['target'],'project_modules':204,'external_imports':inv['direct_external_imports'],'exact_module_set':True,'exact_direct_project_edges':edges,'source_and_all_recorded_companions_current':True,'fresh_objects':objects,'source_warnings':{m:n for m,n in warnings.items() if n},'source_warning_count':sum(warnings.values()),'source_compiler_seconds':seconds,'audits':audits,'historical_failed_attempts':[{'module':r['module'],'index':r['index'],'seconds':r['seconds'],'timed_out':r['timed_out'],'log_sha256':r['log_sha256']}for r in failures],'completed_sha256':sha(P/'completed.json'),'attempts_sha256':sha(P/'attempts.json'),'inventory_sha256':sha(P/'inventory-v3.json'),'toolchain_boundary_sha256':sha(P/'toolchain-boundary-v3.json'),'review_source_sha256':sha(Path(__file__))}
(P/'final-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('exact_direct_project_edges','fresh_objects','source_warnings')},indent=2))
