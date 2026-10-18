from pathlib import Path
import hashlib,json,gzip
W=Path(__file__).resolve().parent
P=W.parent/'zfc244-loop-rotation-20261018'/'zfc244-loop-rotation-20261018'
R=Path('/tmp/zfc244-rotation-root-replay');O=R/'run1';C=R/'copy'
def desc(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def clean(x):
 if isinstance(x,dict):return {k:clean(v) for k,v in x.items() if k not in ['seconds','elapsed_seconds']}
 if isinstance(x,list):return [clean(v) for v in x]
 return x
checks=[]
def eq(label,a,b):
 assert a==b,label
 checks.append(label)
inv=json.loads((W/'inventory.json').read_text());copy=[]
for f in inv['members']:
 p=P/f['relative'];c=C/f['relative'];eq('pristine pin '+f['relative'],hashlib.sha256(p.read_bytes()).hexdigest(),f['sha256']);eq('executed copy '+f['relative'],p.read_bytes(),c.read_bytes());copy.append({'relative':f['relative'],'sha256':f['sha256']})
v=json.loads((O/'verification.json').read_text());e=json.loads((O/'execution.json').read_text());eq('terminal status',v['status'],'PASS_ROOT_ROTATION244_PRIMARY_REPLAY');eq('same commands',v['jobs'],e['jobs']);eq('ordered jobs',[j['job'] for j in v['jobs']],['construct','source','blank','frames','affine','literal','expanded'])
logs=[]
for j in v['jobs']:
 eq(j['job']+' exit',j['returncode'],0);eq(j['job']+' timeout',j['timeout'],False);eq(j['job']+' command assertions',j['command'][1],'-B');eq(j['job']+' script copy',Path(j['command'][2]).parent,C/'code');assert 0<=j['seconds']<600
 for stream in ['stdout','stderr']:
  p=O/(j['job']+'.'+stream+'.log');logs.append(desc(p))
  if stream=='stderr':eq(j['job']+' empty stderr',p.read_bytes(),b'')
 eq(j['job']+' nonempty stdout',bool((O/(j['job']+'.stdout.log')).read_bytes()),True)
for n in ['machine.tm','machine_old.tm','sites_logical.json','sites_physical.json','renumbering.json','boot.json']:
 eq('generated '+n,(O/'built'/n).read_bytes(),(P/'machine'/n).read_bytes())
pairs=[('built/expanded-runtime.json','certificate/expanded-runtime.json'),('built/affine-runtime.json','certificate/affine-runtime.json'),('built/literal-regression.json','certificate/literal-regression.json'),('frames.json','certificate/frame-composition.json'),('built/construction.json','certificate/construction.json'),('blank/independent-blank.json','certificate/independent-blank.json')]
for tail in ['source_verification.json','right/source_verification.json','right/sites_logical.json','right/sites_physical.json','left/source_verification.json','left/sites_logical.json','left/sites_physical.json']:pairs.append(('source/'+tail,'certificate/source-rotation/'+tail))
comparisons=[]
for a,b in pairs:
 x=json.loads((O/a).read_text());y=json.loads((P/b).read_text());eq('semantic fields '+a,clean(x),clean(y));comparisons.append({'fresh':desc(O/a),'delivered':desc(P/b),'comparison':'all fields exact after removing only seconds/elapsed_seconds keys recursively'})
eq('compressed literal fixture payload',gzip.decompress((O/'built/literal-regression-cases.json.gz').read_bytes()),gzip.decompress((P/'certificate/literal-regression-cases.json.gz').read_bytes()))
x=json.loads((O/'built/expanded-runtime.json').read_text());eq('case census',x['counts'],{'cases':8390,'symbolic_rules':2312438});eq('complete',x['complete'],True);eq('progress',x['positive_progress_checked'],True);eq('primary arbitrary',x['arbitrary_primary_registers'],True);eq('suffix arbitrary',x['arbitrary_nonempty_finite_spare_suffix'],True);eq('unused',x['unused_rows'],[[27,1]]);eq('covered rows',x['literal_rows_covered'],487);eq('source context',v['source_context_edges'],8385);eq('blank',v['blank_steps'],407931)
rec={'status':'EXISTING_ROOT_PRIMARY_REPLAY_REVIEW_PASS','reviewer_role':'Independent source/metadata reviewer and intake author; did not author or execute supplied primary algorithms or root runner.','verification':desc(O/'verification.json'),'execution':desc(O/'execution.json'),'runner':desc(R/'replay.py'),'reviewer_source':desc(Path(__file__)),'copy_pairs':copy,'result_comparisons':comparisons,'logs':logs,'checks':len(checks),'findings':[],'scope':'Seven actual root jobs, including one complete expanded runtime replay; independent ordinary proof receipt remains separate. No proof-assistant/PA claim, no discovery search or delivery-manifest work.','expanded_seconds':v['jobs'][-1]['seconds'],'fresh_rules':x['rules'],'auxiliary_status':'Logical certificates already separately PASS by root; later auxiliary jobs excluded from this receipt.'}
(W/'primary-replay-review.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({'checks':len(checks),'sha256':hashlib.sha256((W/'primary-replay-review.json').read_bytes()).hexdigest()}))
