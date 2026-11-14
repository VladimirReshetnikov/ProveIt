import itertools,json
from projection import prefix
count=0
for c in range(5):
 for a in range(4):
  for b in (0,1):
   for n in range(8):
    atoms=(('run',b,(c,a)),('run',1-b,(2,0)),('blank',))
    admitted=set(prefix(atoms,n))
    for x in range(9):
     actual=tuple(([b]*(c+a*x)+[1-b]*2+[0]*20)[:n]);count+=1
     if actual not in admitted:raise ValueError('Projection lost concrete instance')
# Corruption controls are explicit and use no Python assertions.
import copy,check_windows as ck
from pathlib import Path
import tempfile
original=json.loads(Path('windows.json').read_text());tests=[]
for key,value in [('radius',4),('table_sha256','0'*64),('source_sha256','0'*64),('engine_sha256','0'*64),('startup_steps',48139)]:
 o=copy.deepcopy(original);o[key]=value;tests.append(o)
o=copy.deepcopy(original);o['contexts']['0']=[0];tests.append(o)
o=copy.deepcopy(original);o['contexts'].pop('0');tests.append(o)
o=copy.deepcopy(original);o['contexts']['1']=[128];tests.append(o)
for o in tests:
 with tempfile.NamedTemporaryFile(mode='w',suffix='.json') as f:
  json.dump(o,f);f.flush()
  try:ck.check(Path(f.name))
  except ValueError:pass
  else:raise ValueError('Negative control accepted')
print(json.dumps({'status':'PROJECTION_SANITY_PASS','concrete_instances':count,'negative_controls':len(tests),'scope':'Finite sanity and receipt tampering checks, not proof of all-length projection.'}))
