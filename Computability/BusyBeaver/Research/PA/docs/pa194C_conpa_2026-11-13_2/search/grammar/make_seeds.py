import sys,json
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]/'reference/pa194'
sys.path.insert(0,str(BASE/'construction'))
import compiler as c
inc=('leaf','inc',1)
c.MACROS[inc,inc]=99
c.MACROS[(inc,inc),(inc,inc)]=190
paths=[BASE/'construction/source/pa194.grammar.json',Path(__file__).resolve().parents[1]/'reference/pa194_second.grammar.json', BASE/'construction/inputs/parent195S.grammar.json']
rows,_=c.machine();fixed=sorted({q for q,b in rows if q<1300})
out=[str(len(fixed))]
for q in fixed:out.append(' '.join(map(str,[q,*rows[q,0],*rows[q,1]] )).replace('True','1').replace('False','0'))
out.append(str(len(paths)))
for j,p in enumerate(paths):
 t=c.read_grammar(p); nodes=[]; seen={}
 def visit(t):
  if t in seen:return seen[t]
  if t==c.BREAK: row=(0,-1,-1,-1)
  elif t in c.MACROS:row=(0,c.MACROS[t],-1,-1)
  else:row=(1,visit(t[0]),visit(t[1]),0)
  i=len(nodes);seen[t]=i;nodes.append(row);return i
 r=visit(t);out.append(f'{j} {len(nodes)} {r}')
 out.extend(' '.join(map(str,n)) for n in nodes)
Path(__file__).with_name('seeds194.txt').write_text('\n'.join(out)+'\n')
print('wrote seeds',len(paths))
