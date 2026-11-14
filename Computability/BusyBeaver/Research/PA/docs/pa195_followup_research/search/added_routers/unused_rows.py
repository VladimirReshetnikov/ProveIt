import sys,json
from pathlib import Path
P=(Path(__file__).resolve().parent / 'reference_pa195');sys.path.insert(0,str(P));import build_verify as v
c=v.c;rows=v.table(P/'pa195.native.tm');t=c.read_grammar(P/'grammar.json');sites,cfg,cs=c.source(t);seen=set()
def observe(s):
 q,onl,l,r=s
 if onl or not r:return
 x=r[0]
 if x[0]=='b':seen.add((q,x[1]))
 elif x[0]=='r' and (x[2]>0 or x[3]>0):seen.add((q,x[1]))
 elif x[0]=='x':seen.add((q,0))
r=c.validate(rows,cs,observe=observe);print(r,flush=True)
seen.update((q,b) for q in c.BOXSTATES for b in(0,1))
q,head,ones=74,0,set()
for _ in range(58154):
 bit=int(head in ones);seen.add((q,bit));w,d,q=rows[q,bit];(ones.add if w else ones.discard)(head);head+=1 if d else -1
unused={str(k):rows[k] for k in rows if k not in seen};print('UNUSED',unused,flush=True)
(Path(__file__).resolve().parent / 'unused_rows.json').write_text(json.dumps({'validation':r,'rows_accounted':len(seen),'unused':unused},indent=2))
