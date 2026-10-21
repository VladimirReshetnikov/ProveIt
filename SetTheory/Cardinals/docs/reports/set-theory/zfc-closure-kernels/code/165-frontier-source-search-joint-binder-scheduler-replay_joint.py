#!/usr/bin/env python3
from pathlib import Path
import json,sys,tempfile,subprocess
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
import source_language as s
cb=s.tree(json.loads((P/'q13_cb.sites.json').read_text()))
for tag in ['G_Q','G_I']:
 old=s.tree(json.loads((P.parent/(tag+'.json')).read_text()))
 new=(cb[0],old[1])
 assert json.loads(json.dumps(s.sites(new)))==json.loads((P/(tag+'_CB1.json')).read_text())
 print(tag,s.metrics(new))
if '--allocate' in sys.argv:
 out=Path(tempfile.mkdtemp(prefix='zfc-joint-binder-'))
 for tag in ['G_Q','G_I']:
  for base in ['q13_cb215','q13_normal215']:
   dest=out/(tag+'_'+base)
   subprocess.run([sys.executable,str(P/'allocate_joint.py'),'--source',str(P/(tag+'_CB1.json')),'--output',str(dest),'--limit','20','--baseline-table',str(P/(base+'.native.tm')),'--baseline-source',str(P/'q13_cb.sites.json')],check=True,stdout=subprocess.DEVNULL)
   d=json.loads((dest/'allocation.json').read_text())
   assert d['status']=='NO_ALLOCATION',d['status']
   print(tag,base,d['status'])
 print('Fresh replay receipts:',out)
