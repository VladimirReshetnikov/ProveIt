#!/usr/bin/env python3
"""Recreate the four frozen terminal grammar templates."""
import argparse
from common import *
MAC={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,('leaf','inc',1):61,'node60':99,'node61':190}
i=('leaf','inc',1);MAC[(i,i)]=99;MAC[((i,i),(i,i))]=190
r={}
for l in (MACHINE/'raw.native.tm').read_text().splitlines():
 q,b,w,d,n=l.split();r[int(q),int(b)]=(int(w),int(d=='R'),int(n))
qs=sorted(q for q,b in r if b==0 and q<1300)
lines=[str(len(qs))]
for q in qs:lines.append(' '.join(map(str,[q]+list(r[q,0])+list(r[q,1]))))
def replace_last(t,term):
 if isinstance(t,tuple) and len(t)==2:return t[0],replace_last(t[1],term)
 assert t=='node49',t
 return term
def write_templates(variants, output, filename='templates.txt', save_trees=True):
 rows = list(lines)
 rows.append(str(len(variants)))
 counts=[]
 for j,(name,g) in enumerate(variants):
  nodes=[];index={}
  def emit(t):
   if t in index:return index[t]
   if t in MAC:v=(0,MAC[t],-1,-1)
   else:v=(1,emit(t[0]),emit(t[1]),0)
   n=len(nodes);nodes.append(v);index[t]=n;return n
  root=emit(g);rows.append(f'{j} {len(nodes)} {root}')
  rows.extend(' '.join(map(str,n))for n in nodes)
  if save_trees:(output/(name+'.tree.json')).write_text(json.dumps(g)+'\n')
  counts.append({'name':name,'nodes':len(nodes),'readers':len(index)-sum(1 for x in index if x in MAC)})
 (output/filename).write_text('\n'.join(rows)+'\n')
 return counts

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
 a=p.parse_args();out=output_dir(a.output,'ax11g-terminal-templates-')
 variants=[('AX11G',G)]+[(x,replace_last(G,x))for x in ['node55','node58','node70']]
 print(json.dumps(write_templates(variants,out),indent=2));print('output',out)
