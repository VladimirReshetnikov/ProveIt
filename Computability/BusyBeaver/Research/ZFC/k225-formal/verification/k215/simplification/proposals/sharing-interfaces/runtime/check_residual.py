"""Owned transcription of phase9 Home and residual leaf execution. No fetched code executed."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
import json,collections,hashlib
from pathlib import Path
import analyze_symbolic as A
from bind_ports import PORTS
D=Path(__file__).parent
for name,digest in json.loads((D/'INPUT_PINS.json').read_text()).items():
 assert hashlib.sha256((D/name).read_bytes()).hexdigest()==digest, ('Input pin mismatch',name)
T=A.I.table(D/'inputs/K215_Formal.tm');sites=json.loads((D/'inputs/K215_Formal.sites.json').read_text())
def port(pc):
 # Literal table routing on an explicit finite PC window; certify no exterior access.
 bits=[1]+list(map(int,pc));orig=bits.copy();h=1;q=84
 for target in range(2,len(pc)+1):
  for step in range(100):
   assert 0<=h<len(bits)
   w,d,q=T[q,bits[h]];bits[h]=w;h+=d
   if h==target and bits==orig:break
  else:raise AssertionError('decoder routing cap')
 assert h==len(pc) and bits==orig
 assert q==PORTS[pc], ('Formal port mismatch',pc,q,PORTS[pc])
 return q
def home(s):
 q,on,l,r=s
 if q!=2 or not on:return None
 u=list(reversed(l))
 while u and ((u[0][0]=='b' and u[0][1]==0) or (u[0][0]=='r' and u[0][1]==0)):u.pop(0)
 if not u or u.pop(0)!=A.B(1):return None
 k=0
 for x in reversed(u):
  if x[0]=='b':k=0 if x[1] else k+1
  elif x[0]=='r':
   if x[1]:k=k if x[3]==0 else 0
   elif x[2]==0:k+=x[3]
   else:return None
  else:return None
  if k>=8:return None
 return(84,False,(A.B(1),),tuple(u)+r)
def run(site,pos,leaf):
 pc,op,arg=site;br=None;effect=A.X();delta=ov=0
 if op=='CI':succ,ov=A.I.inc(pc);effect=A.X('inc',A.I.PHY[arg])
 elif op=='CD' and pos:succ,ov=A.I.inc(pc);effect=A.X('dec',A.I.PHY[arg]);delta=1;br=(A.I.PHY[arg],False)
 elif op in('CD','CB'):
  succ,ov=A.I.inc(A.I.strip(pc,'0',arg if op=='CB' else 1));br=(A.I.PHY[arg],True)if op=='CD'else None
 elif op=='CC':succ=A.I.strip(pc,'1',arg)
 else:succ=''
 s=(84,False,(A.B(1),),tuple(A.B(int(b))for b in pc)+(A.U(0,1,64-len(pc)),A.B(1),A.X()))
 if leaf:s=(port(pc),False,tuple(A.B(int(b))for b in reversed(pc[:-1]))+(A.B(1),),(A.B(int(pc[-1])),A.U(0,1,64-len(pc)),A.B(1),A.X()))
 e=(84,False,(A.B(1),),tuple(A.B(int(b))for b in succ)+(A.U(0,1,64+delta+ov-len(succ)),A.B(1),effect));ek=A.key(e)
 moved=False;homes=0
 for n in range(4000):
  if moved and ((op=='CH' and s[0]==254)or(op!='CH' and s[0]==84 and not s[1] and A.key(s)==ek)):return n,homes
  h=home(s)
  if h is not None:s=h;moved=True;homes+=1
  else:s,m,_=A.step(T,br,s);moved|=m
 raise AssertionError(('cap',site,pos,leaf))
rows=[]
for i,site in enumerate(sites):
 if i%500==0:print(i,flush=True)
 for pos in([False,True]if site[1]=='CD'else[False]):
  full,h0=run(site,pos,False);res,h1=run(site,pos,True)
  assert res<=full
  rows.append(dict(site=i,positive=pos,port_q=port(site[0]),full_home_steps=full,residual_home_steps=res,home_uses=h1,prefix_length=len(site[0])-1))
out=dict(status='ALL_RESIDUAL_GUARDS_PASS',guards=len(rows),full_home_steps=sum(x['full_home_steps']for x in rows),residual_home_steps=sum(x['residual_home_steps']for x in rows),home_uses=sum(x['home_uses']for x in rows),min_residual=min(x['residual_home_steps']for x in rows),max_residual=max(x['residual_home_steps']for x in rows),records=rows,scope='Owned symbolic checker with existing BoxLemmas assumed; no Lean compilation or build-time claim.')
(D/'RESIDUAL_RESULT.json').write_text(json.dumps(out,separators=(',',':')));print({k:v for k,v in out.items()if k!='records'})
