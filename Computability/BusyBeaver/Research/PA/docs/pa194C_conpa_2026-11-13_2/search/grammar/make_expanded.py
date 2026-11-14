from pathlib import Path
import sys,json
BASE=Path(__file__).resolve().parents[1]/'reference/pa194'
sys.path.insert(0,str(BASE/'construction'))
import compiler as c
inc=('leaf','inc',1)
c.MACROS[inc,inc]=99;c.MACROS[(inc,inc),(inc,inc)]=190
add={'node54':114,'node57':20,'node69':179}
c.MACROS.update(add)
nodes=c.raw_nodes()
def expand(t):
 if t=='node55':return ('node49','node54')
 if t=='node58':return ('node49','node57')
 if t=='node70':return ('node49','node69')
 return tuple(map(expand,t)) if c.isnode(t) else t
paths=[BASE/'construction/source/pa194.grammar.json',Path(__file__).resolve().parents[1]/'reference/pa194_second.grammar.json']
rows,_=c.machine();fixed=sorted({q for q,b in rows if q<1300});out=[str(len(fixed))]
for q in fixed:out.append(' '.join(map(str,[q,*rows[q,0],*rows[q,1]])).replace('True','1').replace('False','0'))
out.append(str(len(paths)))
for j,p in enumerate(paths):
 t=expand(c.read_grammar(p));ns=[];seen={}
 def visit(t):
  if t in seen:return seen[t]
  if t==c.BREAK:row=(0,-1,-1,-1)
  elif t in c.MACROS:row=(0,c.MACROS[t],-1,-1)
  else:row=(1,visit(t[0]),visit(t[1]),0)
  i=len(ns);seen[t]=i;ns.append(row);return i
 r=visit(t);out.append(f'{j} {len(ns)} {r}');out.extend(' '.join(map(str,x)) for x in ns)
Path(__file__).with_name('expanded_seeds.txt').write_text('\n'.join(out)+'\n')
def attr(t):
 if isinstance(t,str):return attr(nodes[t])
 if not c.isnode(t):return (0,0,0,0,int(t==inc))
 a,b=map(attr,t);return (1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4])
lines=(BASE/'search/inputs/leaf_attrs.txt').read_text().splitlines();lines[0]=str(int(lines[0])+len(add))
for n,q in add.items():lines.append(' '.join(map(str,[q,*attr(n)])))
Path(__file__).with_name('expanded_attrs.txt').write_text('\n'.join(lines)+'\n')
print('expanded dictionary',add)
