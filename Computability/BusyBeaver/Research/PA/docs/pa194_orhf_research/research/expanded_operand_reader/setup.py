from pathlib import Path
import json,sys,shutil
ROOT=Path(__file__).resolve().parent
OUT=ROOT
sys.path.insert(0,str(ROOT/'vendor'))
import compiler as c,support as s
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
nodes={k:tup(v)for k,v in json.loads((ROOT/'inputs/AX11H.nodes.json').read_text()).items()}
g=c.read_grammar(ROOT/'inputs/AX11H.grammar.json')
old=s.read_table(ROOT/'inputs/primary.raw.native.tm');fixed={k:v for k,v in old.items()if k[0]<1300};fixed[164,1]=(1,True,114)
for q,b,a in json.loads((ROOT/'inputs/h_shift_edits.json').read_text()):fixed[q,b]=tuple(a)
macros=dict(c.MACROS);macros.update({'node32':104,'node53':107})

def attr(t):
 if isinstance(t,str):return attr(nodes[t])
 if t[0]=='leaf':return(0,0,0,0,int(t[1]=='inc'))
 a,b=map(attr,t)
 return(1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4])
for name in ['node32','node53','node75']:print(name,attr(name))
leafattrs={v:attr(k)for k,v in macros.items()}
leafattrs[-1]=(0,0,0,0,0)
(OUT/'leaf_attrs.txt').write_text(str(len(leafattrs))+'\n'+''.join(str(q)+' '+' '.join(map(str,a))+'\n'for q,a in leafattrs.items()))
A,B,C,D='node32','node53','node55','node65'
def expand(t):
 if t=='node75':return((A,(B,C)),D)
 if c.isnode(t):return tuple(map(expand,t))
 return t
g2=expand(g)
# Explicit instruction identity with expanded macro exposure.
c.machine=lambda:(fixed,[]);c.raw_nodes=lambda:nodes
c.MACROS.update(macros)
_,baseins,_=c.source(g);_,newins,_=c.source(g2);assert newins==baseins

def encode(g):
 ts=[];seen={}
 def rec(t):
  if t in seen:return seen[t]
  if c.isnode(t):l,r=map(rec,t);row=(1,l,r,0)
  else:row=(0,-1 if t==('leaf','breakTo',1)else macros[t],-1,-1)
  i=len(ts);ts.append(row);seen[t]=i;return i
 r=rec(g);return ts,r
parts=[str(len(fixed)//2)]
for q in sorted({q for q,b in fixed}):
 parts.append(' '.join(map(str,[q]+[x for b in range(2)for x in map(int,fixed[q,b])])))
parts.append('1');ts,r=encode(g2);parts.append(f'0 {len(ts)} {r}');parts+=[' '.join(map(str,row))for row in ts]
(OUT/'templates.txt').write_text('\n'.join(parts)+'\n')
(OUT/'source_instructions.json').write_text(json.dumps(baseins)+'\n')
(OUT/'nodes.json').write_text(json.dumps(nodes)+'\n')
(OUT/'fixed.native.tm').write_text(s.table_text(fixed))

lines=(OUT/"templates.txt").read_text().splitlines()
edits={(87,0):(0,1,88),(88,0):(0,0,301),(301,0):(0,1,122),(301,1):(1,1,301)}
for i in range(1,1+int(lines[0])):
 a=list(map(int,lines[i].split()));q=a[0]
 for b in(0,1):
  if(q,b)in edits:a[1+b*3:4+b*3]=edits[q,b]
 lines[i]=" ".join(map(str,a))
(OUT/"templates_B.txt").write_text("\n".join(lines)+"\n")
