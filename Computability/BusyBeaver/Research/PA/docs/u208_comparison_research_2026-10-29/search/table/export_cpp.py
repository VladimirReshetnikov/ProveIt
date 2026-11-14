import sys,pathlib
sys.path.insert(0,'u209_reduction_20261029/table_search')
from core import read,contexts
out=pathlib.Path('u208_reduction_20261029/table_search')
for name in ('4564c487','89145587'):
 t=read(pathlib.Path('u209_reduction_20261029/table_search')/('candidate_'+name)/'native.tm');states=sorted({q for q,b in t});lines=[str(len(states))]
 for q in states:
  cs=contexts(t,q,8) if q else [{}];lines.append(' '.join(map(str,[q,*t[q,0],*t[q,1],len(cs)])))
  for c in cs:lines.append(' '.join(map(str,[len(c),*sum(([p,b] for p,b in c.items()),[])])))
 (out/(name+'.dat')).write_text('\n'.join(lines)+'\n')
