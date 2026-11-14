"""Convert the exploratory finite-window reachability characteristic vectors to cylinders."""
from pathlib import Path
import argparse,json
import numpy as np
p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('output');p.add_argument('--radius',type=int,default=7);a=p.parse_args()
r=a.radius;n=2*r+1;count=1<<n
raw=np.fromfile(a.input,dtype=np.uint8).reshape(512,count)
positions=[0]+[s*i for i in range(1,r+1)for s in(-1,1)];axes=[r-x for x in positions]
def cubes(a,i=0):
 if np.all(a):return[()]
 if not np.any(a):return[]
 if np.array_equal(a[0],a[1]):return cubes(a[0],i+1)
 return[((positions[i],b),)+c for b in(0,1)for c in cubes(a[b],i+1)]
cs={q:cubes(raw[q].reshape((2,)*n).transpose(axes))for q in range(512)if raw[q].any()}
Path(a.output).write_text(json.dumps(cs,separators=(',',':'))+'\n')
print('states',len(cs),'cylinders',sum(map(len,cs.values())))
