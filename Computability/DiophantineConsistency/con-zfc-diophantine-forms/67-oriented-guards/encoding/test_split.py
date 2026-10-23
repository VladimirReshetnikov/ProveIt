#!/usr/bin/env python3
"""Negative controls and isolated replay for the degree-separated certificate."""
import copy,json,subprocess,sys,tempfile,shutil
from pathlib import Path
R=Path(__file__).resolve().parent
cases=[]
def reject(label,fn,filename='split_code.json'):
 with tempfile.TemporaryDirectory() as td:
  d=Path(td)
  for name in ['verify_split.py','parent_source.json','split_code.json','split_kernels.json']:
   shutil.copy2(R/name,d/name)
  data=json.loads((d/filename).read_text());fn(data);(d/filename).write_text(json.dumps(data))
  p=subprocess.run([sys.executable,str(d/'verify_split.py')],capture_output=True,text=True)
  if p.returncode==0:raise ValueError('corruption accepted: '+label)
  cases.append({'case':label,'rejected':True,'reason':p.stderr.strip().splitlines()[-1]})
reject('duplicate variable weights',lambda x:x['weights'].__setitem__(1,x['weights'][0]))
reject('destroy supported label',lambda x:x['weights'].__setitem__(0,4))
reject('perturb target',lambda x:x['targets'].__setitem__(0,x['targets'][0]+1))
reject('duplicate target',lambda x:x['targets'].__setitem__(1,x['targets'][0]))
reject('duplicate row',lambda x:x['order'].__setitem__(1,x['order'][0]))
reject('wrong row operation',lambda x:x['source_row_operations'][0].__setitem__(2,-1))
reject('omit global sign',lambda x:x.__setitem__('global_sign',1))
reject('false kernel degree',lambda x:x['kernel_degrees'].__setitem__(2,1930))
reject('false height',lambda x:x.__setitem__('convolution_height',2160))
reject('change source coefficient',lambda x:x['equations'][0]['terms'][0].__setitem__('coefficient',2),'parent_source.json')
reject('change exported kernel',lambda x:x['kernels'][0]['terms'][0]['coefficient'][0].__setitem__('coefficient',100),'split_kernels.json')
with tempfile.TemporaryDirectory() as td:
 d=Path(td)
 for name in ['verify_split.py','parent_source.json','split_code.json','split_kernels.json']:shutil.copy2(R/name,d/name)
 outputs=[]
 for flag in [[],['-O']]:
  p=subprocess.run([sys.executable]+flag+[str(d/'verify_split.py')],capture_output=True,text=True,check=True);outputs.append(p.stdout)
 if outputs[0]!=outputs[1] or json.loads(outputs[0])!=json.loads((R/'VERIFICATION.json').read_text()):raise ValueError('isolated/optimized replay mismatch')
print(json.dumps({'status':'PASS','isolated_replay':True,'optimized_replay_byte_identical':True,'corruption_controls':cases,'controls_rejected':len(cases)},indent=2))
