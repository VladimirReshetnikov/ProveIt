"""One-time schedule preparation, no search or external algebra."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
for old,new,degree in [('integer14_degree85','integer13_degree118',118),('integer14_degree87','integer13_degree120',120)]:
 src=json.loads((ROOT/'inherited_round22'/(old+'_spec.json')).read_text())
 s={'variables':[v for v in src['variables'] if v!='f'],'registers':[],'degree':degree}
 for n,f in src['registers']:
  if n=='Q':
   s['registers'] += [('Ds','Delta*I**2'),('Fs','Ds+1'),('Q','Delta*Ds'),('delta','Q-1'),('b','c*T-R'),('dy','delta*y'),('t','c+dy'),('tt','t*t'),('Lb','Fs*(b*b)'),('Ares','Lb+tt-Q*dy*y-1'),('Hres','Ares*Ares-4*Lb*tt')]
  elif n in ['V','strong','uu','auxiliary']:continue
  elif n=='P':s['registers'].append(('P','N*Hres+N+Hres'))
  else:s['registers'].append((n,f))
 (ROOT/(new+'_spec.json')).write_text(json.dumps(s,indent=2)+'\n')
