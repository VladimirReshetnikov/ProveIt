from pathlib import Path
import sys,json,shutil
W=Path(__file__).resolve().parent;P=W.parents[1];sys.path.insert(0,str(P/'construction/vendor'))
import compiler as c,support as s
UP=W/'upstream_grammar'
def tu(x):return tuple(map(tu,x))if isinstance(x,list)else x
nodes={k:tu(v)for k,v in json.load(open(W/'nodes.json')).items()}
INC=('leaf','inc',1);MAC=dict(c.MACROS);MAC['nodeDouble']=400
T=tu(json.load(open(W/'grammar.tree.json')))
rows=s.read_table(W/'raw.native.tm');base=sorted({q for q,b in rows if q<1300})
# The new 200-token word has head boundaries recomputed directly from old token edits.
oldbounds=[18,35,54,70,86,102,121]
def words(t):return words(t[0])+words(t[1])if c.isnode(t)else[t]
def expand(t):
 if t=='node60':return(INC,INC)
 if t=='node61':return((INC,INC),(INC,INC))
 return tuple(map(expand,t))if c.isnode(t)else t
old=words(expand(tu(json.load(open(P/'inputs/PA194AX11GH/grammar.tree.json')))))
change={}
for i,t in enumerate(old):
 if t!='node65':continue
 j=i+1
 while j<len(old)and old[j]==INC:j+=1
 tag=j-i-1
 if tag==1:change[i]=1
 if tag==3:change[i]=2;change[i+2]=-1;change[i+3]=-1
bounds=[b+sum(v for k,v in change.items()if k<b)for b in oldbounds]
print('bounds',bounds)
# Exact expanded leaf attributes; m=max leading zero-run in every subtree,
# mi=same statistic on paths whose first leaf is an increment.
def attr(t):
 if isinstance(t,str):return attr(nodes[t])
 if not c.isnode(t):return(0,0,0,0,int(t[1]=='inc'))
 a,b=map(attr,t)
 return(1+max(a[0],b[0]),1+a[1],max(1+a[1],a[2],b[2]),max(a[3],b[3],1+a[1]if a[4]else 0),a[4])
leaves={MAC[k]:k for k in MAC};leaves[-1]=c.BREAK
with open(W/'leaf_attrs.txt','w')as f:
 f.write(str(len(leaves))+'\n')
 for q,t in leaves.items():f.write(' '.join(map(str,(q,*attr(t))))+'\n')
ts=[];ids={}
def go(t):
 if t in ids:return ids[t]
 if t in MAC:v=(0,MAC[t],-1,-1)
 elif t==c.BREAK:v=(0,-1,-1,-1)
 else:v=(1,go(t[0]),go(t[1]),0)
 i=len(ts);ts.append(v);ids[t]=i;return i
r=go(T)
with open(W/'templates.txt','w')as f:
 f.write(str(len(base))+'\n')
 for q in base:f.write(' '.join(map(str,[q]+[int(x)for b in (0,1)for x in rows[q,b]]))+'\n')
 f.write('1\n'+f'0 {len(ts)} {r}\n')
 for tr in ts:f.write(' '.join(map(str,tr))+'\n')
screen=(UP/'screen.cpp').read_text().replace('if(l==99&&r==99)','if(l==61&&r==99)')
(W/'screen.cpp').write_text(screen)
src=(UP/'search.cpp').read_text()
src=src.replace('lo[]={18,35,54,70,86,102},hi[]={35,54,70,86,102,121}',f'lo[]={{{",".join(map(str,bounds[:-1]))}}},hi[]={{{",".join(map(str,bounds[1:]))}}}')
src=src.replace('case 190:return "\\\"node61\\\"";','case 190:return "\\\"node61\\\"";case 400:return "\\\"nodeDouble\\\"";')
src=src.replace('(q==190?4:1)','(q==190?3:1)')
src=src.replace('ns.score<=62','ns.score<=76').replace('ns.eff<=59','ns.eff<=56')
(W/'search.cpp').write_text(src)
print('template states',len(base),'attributes',len(leaves),'grammar',len(ts),'root',r)
