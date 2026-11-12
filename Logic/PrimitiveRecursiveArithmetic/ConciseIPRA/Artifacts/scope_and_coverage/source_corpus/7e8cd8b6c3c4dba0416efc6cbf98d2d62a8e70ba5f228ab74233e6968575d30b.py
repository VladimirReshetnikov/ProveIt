"""Three targeted unsafe-control checks for the triplicate protocol.

The mutated programs are intentionally unsound and kept only in temporary
folders for this diagnostic. None is a deliverable checker.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]
KERNEL=ROOT/'code/checker_bytes.py'
source=KERNEL.read_text()
zero_iterator=[0,0,0]
computation_equality=[zero_iterator,0]
comp=[0,zero_iterator,0,0]
reflex=[computation_equality,zero_iterator,0,[3,0]]
false_transport=[computation_equality,0,[0],[0,3]]
controls=[
 {'name':'remove_unary_introduction_arity','old':'i(*a, t, 2)','new':'i(a[0], t, 2)','certificate':[[0,0,0,[0,0]],[[0,0],[0]]],'false_statement':'0 = 1, with the left zero encoded by an inert binary numerical node'},
 {'name':'remove_major_endpoint_agreement','old':'m in ([s, u], not s and [t] * 3) and ','new':'','certificate':[comp,comp,reflex,comp,false_transport,[0,[0]]],'false_statement':'0 = 1'},
 {'name':'remove_recursive_state_substitution','old':'i(r, s, 3) if u else t','new':'r if u else t','certificate':[[[],[0,[0],3],1,0],[[[0],[0],3],0]],'false_statement':'I(1,1;v.v) = 0'},
]
rows=[]
with tempfile.TemporaryDirectory(prefix='ipra-unsafe-control-') as temp:
 for control in controls:
  if source.count(control['old'])!=1:raise ValueError('Kernel spelling changed: '+control['name'])
  mutant=Path(temp)/(control['name']+'.py')
  mutant.write_text(source.replace(control['old'],control['new']))
  for optimized in (False,True):
   verdicts={}
   for label,path in [('correct',KERNEL),('unsafe',mutant)]:
    command=[sys.executable]+(['-O'] if optimized else [])+[str(path)]
    run=subprocess.run(command,input=json.dumps(control['certificate']),text=True,capture_output=True,timeout=8)
    verdicts[label]=run.returncode==0 and run.stdout=='ACCEPT\n'
   row={'name':control['name'],'optimized':optimized,'false_statement':control['false_statement'],'certificate':control['certificate'],'correct_accepted':verdicts['correct'],'unsafe_accepted':verdicts['unsafe'],'pass':not verdicts['correct'] and verdicts['unsafe']}
   rows.append(row)
receipt={'kernel':str(KERNEL.relative_to(ROOT)),'kernel_sha256':hashlib.sha256(KERNEL.read_bytes()).hexdigest(),'controls':3,'public_process_runs':12,'all_pass':all(x['pass'] for x in rows),'results':rows,'scope':'Targeted negative controls demonstrate that three actual mathematical checks block false conclusions; they are not a universal proof.'}
(ROOT/'evidence/mutation_controls.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
if not receipt['all_pass']:raise SystemExit(1)
