from pathlib import Path
from copy import deepcopy
import json
from check import verify
P=Path(__file__).resolve().parent;raw=(P/'inputs/compatibility.sites.json').read_bytes();cert=json.loads((P/'certificate.json').read_text());rows=[]
for name in ['missing seed','missing successor','wrong graph','wrong source','false zero guard']:
 c=deepcopy(cert);b=raw
 if name=='missing seed':c['states'][136]=None
 elif name=='missing successor':c['states'][137]=None
 elif name=='wrong graph':c['graph'][0][0]=0
 elif name=='wrong source':b=raw+b' '
 else:c['states'][3847][1]=2
 try:verify(b,c)
 except (ValueError,IndexError,TypeError)as e:rows.append({'case':name,'status':'REJECTED','reason':str(e)})
 else:raise RuntimeError('mutation accepted '+name)
print(json.dumps({'status':'PASS','controls':rows},indent=2))
