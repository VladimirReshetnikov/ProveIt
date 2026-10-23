#!/usr/bin/env python3
from pathlib import Path
import gzip,hashlib,json
R=Path(__file__).resolve().parents[1]
def req(v,m):
 if not v:raise ValueError(m)
def binding(folder):
 out={}
 for name in ['beta','K','MC','MF_source']:
  b=gzip.decompress((R/folder/(name+'.bin.gz')).read_bytes());out[name]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'bits':int.from_bytes(b,'little').bit_length()}
 return out
main={f:binding(p) for f,p in [('nine','nine/coefficients/old_tuple'),('signed108trim','signed108trim/data'),('signed13','signed13/coefficients')]}
req(all(v==main['nine'] for v in main.values()),'three main source tuple hashes must agree')
q=binding('quartic/upstream/q45/upstream/34-integer14/coefficients/payloads')
p=binding('positive/coefficients/coefficients')
req(q!=main['nine'],'package34 tuple must not be conflated with original31')
req(p['beta']['bits']==590069 and q['beta']['bits']==1064921,'explicit native radix sizes')
# Local artifact manifests must remain exact for the files they name.
for n,h in json.loads((R/'encoding/MANIFEST.json').read_text()).items():req(hashlib.sha256((R/'encoding'/n).read_bytes()).hexdigest()==h,'encoding manifest '+n)
for n,h in json.loads((R/'nine/GENERATED_HASHES.json').read_text()).items():req(hashlib.sha256((R/'nine'/n).read_bytes()).hexdigest()==h,'nine generated hash '+n)
res={'status':'PASS','original31_families':main,'quartic_package34':q,'positive_compact':p,'statement':'Whole tuples authenticated separately; same radix exponent does not identify a tuple.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
