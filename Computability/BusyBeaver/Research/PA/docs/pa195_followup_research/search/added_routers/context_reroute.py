from pathlib import Path
import sys,json,collections,itertools,time
P=(Path(__file__).resolve().parent / 'reference_pa195');sys.path.insert(0,str(P));import build_verify as v
c=v.c;OUT=Path(__file__).resolve().parent;rows=v.table(P/'pa195.native.tm');t=c.read_grammar(P/'grammar.json');sites,cfg,cs=c.source(t)
nextbits=collections.defaultdict(set);byrow=collections.defaultdict(set)

def headbits(s):
 q,onl,l,r=s;seg=l if onl else r
 for x in seg:
  if x[0]=='b':return{x[1]}
  if x[0]=='r':
   if x[3]>0:return{x[1]}
   if x[2]>0:return{0,1}
  else:return{0}
 return{0}

def observe(ci,br,s):
 q,onl,l,r=s
 if onl or not r:return
 x=r[0]
 if x[0]=='b':
  bit=x[1];k=q,bit;byrow[k].add(ci);w,d,n=rows[k];s2=((n,False,(c.BIT[w],)+l,r[1:]) if d else(n,True,l,(c.BIT[w],)+r[1:]));nextbits[k]|=headbits(s2)
 elif x[0]=='r' and (x[2]>0 or x[3]>0):
  k=q,x[1];byrow[k].add(ci)
  if rows.get(k) and rows[k][1] and rows[k][2]==q:nextbits[k]|={0,1}
 elif x[0]=='x':
  byrow[q,0].add(ci)
  if q not in c.BOXSTATES:
   w,d,n=rows[q,0]
   if not w and not d:nextbits[q,0]|=headbits((n,True,l,r))
for ci,cc in enumerate(cs):
 assert c.run(rows,cc,observe=lambda s:observe(ci,cc[1],s)) is not None
# Protect hidden macro entries conservatively.
for q in c.BOXSTATES:
 for bit in(0,1):nextbits[q,bit]|={0,1}
# Include the entire literal initializer.
q,head,ones=74,0,set()
for _ in range(58154):
 bit=int(head in ones);k=q,bit;w,d,q=rows[k];(ones.add if w else ones.discard)(head);head+=1 if d else-1;nextbits[k].add(int(head in ones))

states=sorted({q for q,b in rows});incoming=collections.defaultdict(list)
for k,act in rows.items():incoming[act[2]].append(k)
byact=[collections.defaultdict(list),collections.defaultdict(list)]
for q in states:
 for b in(0,1):byact[b][rows[q,b]].append(q)

summary={};eliminable=[];freerows=[]
for h in states:
 if h==74 or h in c.BOXSTATES:continue
 entries=incoming[h];details=[{'row':k,'bits':sorted(nextbits[k])} for k in entries];summary[str(h)]=details
 options=[]
 for k in entries:
  bs=nextbits[k]
  if len(bs)!=1 or k[0] in c.BOXSTATES or k[0]==h:break
  bit=next(iter(bs));us=[u for u in byact[bit][rows[h,bit]] if u!=h]
  if not us:break
  options.append((k,bit,us))
 else:
  if options:eliminable.append((h,options))
 for bit in(0,1):
  es=[k for k in entries if bit in nextbits[k]]
  us=[u for u in byact[bit][rows[h,bit]] if u!=h]
  if us and es and all(nextbits[k]=={bit} and k[0] not in c.BOXSTATES and k[0]!=h for k in es):freerows.append((h,bit,es,us))
print('ELIMINABLE',eliminable,flush=True);print('FREEABLE',freerows,flush=True)
results=[]
for h,opts in eliminable:
 for targets in itertools.islice(itertools.product(*(x[2] for x in opts)),100):
  rr=rows.copy();edits=[]
  for (k,bit,us),u in zip(opts,targets):
   w,d,n=rr[k];rr[k]=(w,d,u);edits.append([*k,*rr[k]])
  rr.pop((h,0));rr.pop((h,1))
  rv=c.validate(rr,cs)
  print('TRY',h,targets,rv,flush=True)
  if not rv['ok']:continue
  labels=[74]+sorted({q for q,b in rr}-{74})+[254];rev={q:i for i,q in enumerate(labels)};dense={(rev[q],b):(w,d,rev[n]) for(q,b),(w,d,n)in rr.items()};st=v.startup(dense,labels)
  name='reroute194_'+str(h);(OUT/(name+'.native.tm')).write_bytes(v.table_bytes(rr));(OUT/(name+'.tm')).write_bytes(v.table_bytes(dense));(OUT/(name+'.labels.json')).write_text(json.dumps(labels));data={'deleted':h,'edits':edits,'runtime':rv,'startup':st,'entries':summary[str(h)]};(OUT/(name+'.validation.json')).write_text(json.dumps(data,indent=2));results.append(data);print('SUCCESS',name,flush=True);break
(OUT/'context_reroute_census.json').write_text(json.dumps({'nextbits':{str(k):sorted(bs)for k,bs in nextbits.items()},'incoming':summary,'eliminable':eliminable,'freeable':freerows,'successes':results},indent=2))
print('DONE',len(results),flush=True)
