#!/usr/bin/env python3
"""Review existing replay metadata only; no supplied code import or machine run."""
from pathlib import Path
import hashlib,json,gzip,ast,difflib
B=Path('/tmp/zfc243-root-replay');O=Path('/tmp/zfc243-combined-candidate')
R=Path('/tmp/zfc244-rotation-root-replay/copy/reference/baseline245')
P=Path('/tmp/zfc244-d91a27b462-inspection/zfc244-loop-rotation-20261018/zfc244-loop-rotation-20261018')
count=0
def check(v):
 global count
 assert v
 count+=1
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
def load(p):return json.loads(Path(p).read_text())
q=load(B/'quick-verification.json');ex=load(B/'quick-execution.json')
check(q['status']=='PASS_COMBINED243_BLANK_AFFINE_LITERAL' and q['commands']==ex)
check(q['before']==q['after'] and len(q['before'])==9)
for p,h in q['before'].items():check(sha(p)==h)
check((B/'replay.py').read_bytes()==Path('/tmp/zfc243-root-replay.py').read_bytes())
for n in ['machine.tm','machine_old.tm','renumbering.json','sites_logical.json','sites_physical.json']:
 check((B/'candidate'/n).read_bytes()==(O/n).read_bytes())
adapter=load(B/'adapters/adapter-source-review.json')
for key in ['blank','runtime','literal']:
 row=adapter[key]
 for label in ['original','preserved_original','adapter','diff']:
  check(sha(row[label]['path'])==row[label]['sha256'])
 a=Path(row['adapter']['path']);orig=Path(row['original']['path'])
 check((B/'adapters'/a.name).read_bytes()==a.read_bytes())
 check((B/'adapters/original'/orig.name).read_bytes()==orig.read_bytes())
 check((B/'adapters'/(a.name+'.diff')).read_bytes()==Path(row['diff']['path']).read_bytes())
 expected=''.join(difflib.unified_diff(orig.read_text().splitlines(True),a.read_text().splitlines(True),fromfile=str(orig),tofile=str(a)))
 check(expected==Path(row['diff']['path']).read_text())
 ast.parse(a.read_text())
reference_files=[]
for p in sorted((P/'reference/baseline245').rglob('*')):
 if not p.is_file() or p.name=='SHA256SUMS':continue
 rel=p.relative_to(P/'reference/baseline245');live=R/rel
 check(live.is_file() and live.read_bytes()==p.read_bytes());reference_files.append(d(live))
for row,job in zip(ex,['blank','affine','literal']):
 check(row['job']==job and row['exit_code']==0 and row['timeout'] is False)
 check(row['command'][1]=='-B' and '-O' not in row['command'])
 check('--step-limit' not in row['command'] and '--boot-limit' not in row['command'])
 check((B/(job+'.stderr.log')).read_bytes()==b'')
 check('Traceback' not in (B/(job+'.stdout.log')).read_text())
check(len(ex)==3)
blank=load(B/'blank/independent-blank.json');discovery=load(B/'blank/blank-discovery.json')
affine=load(B/'candidate/affine-runtime.json');literal=load(B/'candidate/literal-regression.json')
fixtures=json.loads(gzip.decompress((B/'candidate/literal-regression-cases.json.gz').read_bytes()))
check(blank['blank_steps']==discovery['blank_steps']==q['blank_steps']==407967)
check(blank['discovery_sha256']==sha(B/'blank/blank-discovery.json'))
check((blank['working_states'],blank['transitions'],blank['start'],blank['halt'],blank['dispatcher'])==(243,486,0,243,87))
check(blank['sparse_dense_exact_agreement_both_numberings'] and blank['all_other_cells_zero'])
check(blank['boot_limit']==3000000)
ones={-6,176};pos=177
for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
 ones.update(range(pos+1,pos+value+2));pos+=value+2
check(sorted(ones)==blank['all_one_positions']==discovery['all_one_positions'] and len(ones)==351)
check(blank['spare_values']==discovery['spare_values']==[1]*167)
check(blank['logical_registers']==[3,0,0,0,3,0,0,0,0])
for n in ['machine.tm','machine_old.tm']:
 check((B/'blank'/n.replace('machine','zfc243')).read_bytes()==(B/'candidate'/n).read_bytes())
check(blank['table_sha256']==sha(B/'candidate/machine.tm'))
check(blank['old_table_sha256']==affine['table_sha256']==literal['table_sha256']==sha(B/'candidate/machine_old.tm'))
check(affine['sites_logical_sha256']==literal['source_sha256']==sha(B/'candidate/sites_logical.json'))
check(affine['status']=='PASS_UNIVERSAL_AFFINE_RUNTIME' and affine['complete'])
check(affine['frame_padding']==64 and affine['positive_progress_checked'])
check(affine['arbitrary_primary_registers'] and affine['arbitrary_nonempty_finite_spare_suffix'])
check(affine['literal_rows_covered'] is None and affine['unused_rows'] is None)
logical=load(B/'candidate/sites_logical.json');physical=load(B/'candidate/sites_physical.json')
phys=[6,2,0,4,3,7,8,5,1]
for (p,op,r),(pp,oo,rr) in zip(logical,physical):check((p,op,phys[r] if op in ['CI','CD'] else r)==(pp,oo,rr))
def signatures(sites):
 return [(i,p,op,r,z) for i,(p,op,r) in enumerate(sites) for z in ([True,False] if op=='CD' else [None])]
for records,sites in [(affine['cases'],physical),(fixtures,logical)]:
 check(len(records)==8390)
 for row,sig in zip(records,signatures(sites)):
  check(tuple(row[k] for k in ['index','pc','op','r','zero'])==sig)
check(sum(x['symbolic_rules'] for x in affine['cases'])==sum(affine['rules'].values()))
check(min(x['minimum_literal_steps'] for x in affine['cases'])==13)
check(literal['status']=='PASS_FINITE_LITERAL_REGRESSION' and literal['whole_tape_endpoints_checked'])
check(sum(x['steps'] for x in fixtures)==literal['literal_steps']==q['literal_steps']==6473394)
check((min(x['steps'] for x in fixtures),max(x['steps'] for x in fixtures))==(13,1464))
check(sum(x[2] for x in literal['row_counts'])==6473394 and len(literal['row_counts'])==485)
for serial,row in enumerate(fixtures):
 i=row['index'];op=row['op'];r=row['r'];z=row['zero']
 values=[(17*serial+11*j+3*i+7)%23 for j in range(9)]
 if op=='CD':values[r]=0 if z else 1+(13*serial+7*r)%23
 check(values==row['logical_registers'])
 check(row['spare_values']==[(serial+2*j+3)%13 for j in range(1+serial%5)])
 check(row['initial_span']==64+17*(serial%3) and row['steps']<=20000)
 check(row['final_state']==(254 if op=='CH' else 96))
check(literal['unused_runtime_rows']==[[27,1]])
for job,obj,exclude in [('blank',blank,{'all_one_positions','spare_values'}),('affine',affine,{'cases','literal_rows'}),('literal',literal,{'row_counts'})]:
 text=(B/(job+'.stdout.log')).read_text();start=text.find('{\n')
 parsed=json.loads(text[start:]);check(parsed=={k:v for k,v in obj.items() if k not in exclude})
result={'status':'EXISTING_QUICK_REPLAY_EVIDENCE_REVIEW_PASS','findings':[],
 'verification':d(B/'quick-verification.json'),'execution':d(B/'quick-execution.json'),'reviewer_source':d(__file__),'checks':count,
 'outputs':[d(B/f) for f in ['blank/independent-blank.json','blank/blank-discovery.json','candidate/affine-runtime.json','candidate/literal-regression.json','candidate/literal-regression-cases.json.gz']],
 'logs':[d(B/(j+s+'.log')) for j in ['blank','affine','literal'] for s in ['.stdout','.stderr']],
 'tracked_current_before_after_inputs':q['before'],'current_reference_files':reference_files,
 'input_scope':'All9 quick tracked inputs have exact before/after/current identity. The copied reference payload is currently byte-identical to pristine delivered baseline, excluding the intentionally ignored checksum manifest; that comparison is not an invented quick-run historical before snapshot.',
 'adapter_review':'Full three adapters, exact diffs, preserved originals and root serial runner read. Runtime/literal semantic engines unchanged; blank time discovered under3,000,000 bound then independently verified sparse/dense in both labelings.',
 'results':{'blank_steps':407967,'affine_cases':8390,'literal_cases':8390,'literal_steps':6473394,'literal_rows':485,'unused_row':[27,1],'minimum_positive_constant':13},
 'limits':'Root jobs bounded600seconds each; supplied default literal20,000steps and blank3,000,000 discovery bound unchanged. No compiler or guard run in this review.',
 'scope':'Exact finite complete blank frame; all-case affine replay using inherited box contracts; finite literal fixtures. Expanded actual-table block/whole-frame proof remains separate, and no Lean/PA endpoint is asserted.',
 'reviewer_role':'Independent existing-evidence/adapter reviewer; author of separate pending Lean invariant/blocks/simulation ports, not adapters, runner or actual execution.'}
(B/'independent-review/quick-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'checks':count,'review':d(B/'independent-review/quick-review.json')},indent=2))
