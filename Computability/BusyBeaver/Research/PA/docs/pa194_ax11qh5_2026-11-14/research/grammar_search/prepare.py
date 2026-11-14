#!/usr/bin/env python3
"""Export the exact AX11QH5 fixed engine and source grammar for scoped search."""
import argparse,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/'construction'))
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output',type=Path,default=HERE,help='Directory for input.txt and leaf_attrs.txt; use a fresh replay directory to preserve the recorded inputs.')
a=p.parse_args()
OUT=a.output.resolve()
OUT.mkdir(parents=True,exist_ok=True)
import build
c=build.c;s=build.s
raw,ns,old=build.setup();g=build.replace_exit(old)
fixed={k:v for k,v in raw.items() if k[0]<1300}
assert len(fixed)==270
vals=[];ix={}
def visit(t):
    if t in ix:return ix[t]
    if c.isnode(t):row=(1,visit(t[0]),visit(t[1]),0)
    else:row=(0,c.MACROS[t],-1,-1)
    i=len(vals);ix[t]=i;vals.append(row);return i
root=visit(g)
lines=[str(len(fixed)//2)]
for q in sorted({q for q,b in fixed}):
    lines.append(' '.join(map(str,[q]+[int(x)for b in (0,1)for x in fixed[q,b]])))
lines+=['1',f'0 {len(vals)} {root}']+[' '.join(map(str,row)) for row in vals]
(OUT/'input.txt').write_text('\n'.join(lines)+'\n')
def attr(t):
    if isinstance(t,str):return attr(ns[t])
    if not c.isnode(t):return (0,0,0,0,int(t[0]=='leaf' and t[1]=='inc'))
    a,b=map(attr,t)
    return(1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4])
attrs=[]
for name,q in c.MACROS.items():attrs.append((q,*attr(name)))
attrs.append((-1,0,0,0,0,0))
attrs=list(dict.fromkeys(attrs))
(OUT/'leaf_attrs.txt').write_text(str(len(attrs))+'\n'+'\n'.join(' '.join(map(str,a))for a in attrs)+'\n')
print(json.dumps({'fixed_states':len(fixed)//2,'tree_nodes':len(vals),'root':root,'attributes':attrs}))
