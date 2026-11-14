from pathlib import Path
import json
lo=[18,35,54,70,86,102];hi=[35,54,70,86,102,121]
macros={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221}
paths=[Path('inputs/primary.grammar.json'),Path('inputs/alternative.grammar.json')]
for reg,qfinal in ((3,17),(4,144),(5,45),(6,21)):
 fixed=Path(f'inputs/seed194CSZZ{reg}_mixed.txt' if reg!=6 else 'inputs/seed194CSZZ_mixed.txt').read_text().splitlines();nb=int(fixed[0]);out=fixed[:nb+1]+['2']
 for tid,p in enumerate(paths):
  d=json.loads(p.read_text());rs=d['rules']
  def tree(t):
   if isinstance(t,list):return 61 if t[1]=='inc' else qfinal
   if t in rs:return tuple(map(tree,rs[t]))
   if t=='node60':return(61,61)
   if t=='node61':return((61,61),(61,61))
   return macros[t]
  t=tree(d['root']);ns=[];index={}
  def put(v):
   if v not in index:index[v]=len(ns);ns.append(v)
   return index[v]
  def walk(t,pos):
   if isinstance(t,int):
    if t in (98,12,166):
     for h in range(6):
      if lo[h]<=pos<hi[h]:return put((0,t,h,(98,12,166).index(t))),pos+1
    return put((0,t,-1,-1)),pos+1
   a,pos=walk(t[0],pos);b,pos=walk(t[1],pos);return put((1,a,b,0)),pos
  rt,count=walk(t,0);assert count==190;out.append(f'{tid} {len(ns)} {rt}');out.extend(' '.join(map(str,v))for v in ns)
 Path(f'parameterZ{reg}.txt').write_text('\n'.join(out)+'\n')
s=Path('screen.cpp').read_text().replace('v.effective<=61','v.effective<=59').replace('v.effective<=63','v.effective<=59');Path('parameter_screen.cpp').write_text(s)
