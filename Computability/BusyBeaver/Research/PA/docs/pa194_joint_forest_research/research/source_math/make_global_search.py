from make_dup_seeds import *
import csv
FAM=HERE/'inputs/shared_forest'
DOCS=corpus_docs()
OUT=HERE/'global_search';OUT.mkdir(exist_ok=True)
# Adapt the inherited score engine to the exact fixed forest.
src=(HERE/'screen.cpp').read_text().replace('if(l==99&&r==99){value[i]=190;continue;}','if(l==98&&r==90){value[i]=330;continue;}\n  if(l==61&&r==99){value[i]=336;continue;}')
(OUT/'screen.cpp').write_text(src)
src=(HERE/'search.cpp').read_text().replace('case 213:return','case 332:return').replace('if(ns.eff<=59&&!ns.pen&&hits<200)','if(ns.eff<=57&&!ns.pen&&hits<200)')
(OUT/'search.cpp').write_text(src)
# Literal fixed rows from root's exact validated family.
rows={}
for line in(FAM/'raw.native.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
 if q<1300:rows[q,b]=(w,int(d=='R'),n)
fixed=[str(len(rows)//2)]+[' '.join(map(str,[q,*rows[q,0],*rows[q,1]]))for q in sorted({q for q,b in rows})]
assert len(rows)//2==136
# Expand source trees to compute exact scanner attributes.
nodes=json.loads((FAM/'nodes.json').read_text())
def attr(t):
 if isinstance(t,str):return attr(nodes[t])
 if len(t)==3 and t[0]=='leaf':return(0,0,0,0,int(t[1]=='inc'))
 a,b=map(attr,t);return(1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4])
md={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':332,'node142':194,'node150':221,INC:61,'node60':99,'node61':190}
attrs=[(q,attr(list(t) if isinstance(t,tuple)else t))for t,q in md.items()]+[(-1,(0,0,0,0,0))]
(OUT/'leaf_attrs.txt').write_text(str(len(attrs))+'\n'+'\n'.join(' '.join(map(str,[q,*a]))for q,a in attrs)+'\n')
# Gather canonical190-token shapes from current corpus.
basewords={tuple(word(s)) for s in shapes};allsh={str(s):s for s in shapes}
for p in DOCS.rglob('*grammar.json'):
 try:
  d=json.loads(p.read_text())
  if not isinstance(d,dict)or not isinstance(d.get('rules'),dict)or 'root'not in d:continue
  t=read(p);w=word(t)
  if len(w)!=190:continue
  if isinstance(w[-1],tuple)and w[-1][0]=='leaf':w[-1]='node49';t=adapt(t,w)
  if tuple(w)in basewords:allsh.setdefault(str(t),t)
 except (ValueError,KeyError,TypeError,RecursionError,AssertionError):pass
MACROS['node75']=332
text=fixed+[str(len(allsh))]
for tid,t in enumerate(allsh.values()):
 ns,root=tarray(t);text.append(f'{tid} {len(ns)} {root}');text.extend(' '.join(map(str,row))for row in ns)
(OUT/'original.templates.txt').write_text('\n'.join(text)+'\n')
# Retain the4117 strongest truth-padding seeds; preserve each exacttree.
wanted={int(r['id'])for r in csv.DictReader((HERE/'many_padding_scores.csv').open())if int(r['score'])==61}
f=(HERE/'many_padding.templates.txt').open();nb=int(next(f));[next(f)for _ in range(nb)];nt=int(next(f));text=fixed+[str(len(wanted))]
for j in range(nt):
 ident,n,root=map(int,next(f).split());rr=[list(map(int,next(f).split()))for _ in range(n)]
 if ident not in wanted:continue
 for row in rr:
  if not row[0]and row[1]==213:row[1]=332
 text.append(f'{ident} {n} {root}');text.extend(' '.join(map(str,row))for row in rr)
(OUT/'padding.templates.txt').write_text('\n'.join(text)+'\n')
print('Fixed',len(rows)//2,'Originalshapes',len(allsh),'Padding',len(wanted));print('attrs',attrs)
