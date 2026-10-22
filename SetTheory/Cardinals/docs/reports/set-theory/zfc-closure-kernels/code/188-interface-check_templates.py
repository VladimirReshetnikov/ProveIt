"""Owned prefix-opaque symbolic discovery checker. Not a kernel proof."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
import json,collections,hashlib
from pathlib import Path
import analyze_symbolic as A
D=Path(__file__).parent
for path,digest in json.loads((D/'INPUT_PINS.json').read_text()).items():
 assert hashlib.sha256((D/path).read_bytes()).hexdigest()==digest
T=A.table(D/'inputs/K215_Formal.tm');sites=json.loads((D/'inputs/K215_Formal.sites.json').read_text());ports=json.loads((D/'PORT_BINDING.json').read_text())['ports']
P=('p',0);PR=('p',1)
def prefix_ok(p):return bool(p) and p[-1]=='1' and '00000000'not in p
def step_checked(br,s):
 q,on,l,r=s;side=l if on else r
 assert not(side and side[0][0]=='p'),'Attempted opaque-prefix read'
 return A.step(T,br,s)
def rev(xs):return tuple((P if x==PR else PR if x==P else x)for x in reversed(xs))
def home(s):
 q,on,l,r=s
 if q!=2 or not on:return None
 u=list(rev(l))
 while u and ((u[0][0]=='b'and u[0][1]==0)or(u[0][0]=='r'and u[0][1]==0)):u.pop(0)
 if not u or u.pop(0)!=A.B(1):return None
 k=0;back=rev(u)
 for j,x in enumerate(back):
  if x==PR:
   # Prefix reverse begins1, has no eight-zero run; it must be the final chunk.
   if j!=len(back)-1:return None
   k=7
  elif x[0]=='b':k=0 if x[1]else k+1
  elif x[0]=='r':
   if x[1]:k=k if x[3]==0 else 0
   elif x[2]==0:k+=x[3]
   else:return None
  else:return None
  if k>=8:return None
 return(84,False,(A.B(1),),tuple(u)+r)
def prepare(site,pos):
 pc,op,arg=site;br=None;effect=A.X();delta=ov=0
 if op=='CI':succ,ov=A.I.inc(pc);effect=A.X('inc',A.I.PHY[arg])
 elif op=='CD'and pos:succ,ov=A.I.inc(pc);effect=A.X('dec',A.I.PHY[arg]);delta=1;br=(A.I.PHY[arg],False)
 elif op in('CD','CB'):
  succ,ov=A.I.inc(A.I.strip(pc,'0',arg if op=='CB'else 1));br=(A.I.PHY[arg],True)if op=='CD'else None
 elif op=='CC':succ=A.I.strip(pc,'1',arg)
 else:succ=''
 return succ,br,effect,delta,ov
def attempt(site,pos,cut):
 pc,op,arg=site;succ,br,effect,delta,ov=prepare(site,pos)
 if cut and (not succ.startswith(pc[:cut])or not prefix_ok(pc[:cut])):return None
 suffix=pc[cut:];end=succ[cut:]
 s=(ports[pc],False,tuple(A.B(int(b))for b in reversed(suffix[:-1]))+((PR,)if cut else())+(A.B(1),),(A.B(int(suffix[-1])),A.U(0,1,16),A.B(1),A.X()))
 target=(84,False,(A.B(1),),((P,)if cut else())+tuple(A.B(int(b))for b in end)+(A.U(0,1,16+delta+ov+len(pc)-len(succ)),A.B(1),effect));ek=A.key(target);moved=False;hs=0
 try:
  for n in range(4000):
   if moved and ((op=='CH'and s[0]==254)or(op!='CH'and s[0]==84 and not s[1]and A.key(s)==ek)):
    return((bool(cut),ports[pc],suffix,op,arg,pos,end,delta,ov,len(pc)-len(succ)),n,hs)
   h=home(s)
   if h is not None:s=h;moved=True;hs+=1
   else:
    # Reject attempts to read an opaque cell. Only the proved-style Home rule crosses P.
    q,on,l,r=s;side=l if on else r
    if side and side[0][0]=='p':return None
    s,m,_=step_checked(br,s);moved|=m
 except (AssertionError,KeyError):return None
 return None
def syntactic_frame(k):
 opaque,q,suffix,op,arg,pos,end,delta,ov,diff=k
 if not opaque:return True
 if op=='CC':return suffix.count('1')>=arg and A.I.strip(suffix,'1',arg)==end
 if op=='CB':
  tail=A.I.strip(suffix,'0',arg);result,overflow=A.I.inc(tail)
  return suffix.count('0')>=arg and not overflow and result==end
 return False
rows=[];templates={};fallback=0
for i,site in enumerate(sites):
 if i%500==0:print(i,flush=True)
 pc=site[0]
 for pos in([False,True]if site[1]=='CD'else[False]):
  found=None
  for cut in list(range(len(pc)-1,0,-1))+[0]:
   found=attempt(site,pos,cut)
   if found:break
  assert found,(i,site,pos)
  key,steps,hs=found
  assert syntactic_frame(key), ('Source prefix framing failed',key)
  if key not in templates:templates[key]=len(templates)
  rows.append(dict(site=i,positive=pos,cut=cut,template=templates[key],steps=steps));fallback+=not bool(cut)
out=dict(status='OPAQUE_PREFIX_TEMPLATE_DISCOVERY_PASS',guards=len(rows),templates=len(templates),opaque_templates=sum(k[0]for k in templates),literal_templates=sum(not k[0]for k in templates),literal_guard_uses=fallback,records=rows,template_keys=[list(k)for k in templates],scope='Owned symbolic model with new opaque-prefix Home lemma assumed; not a Lean/Rocq theorem.')
out['literal_control_exceptions']=[sites[r['site']] for r in rows if not r['cut'] and sites[r['site']][1]in('CB','CC')]
out['opaque_guard_uses']=len(rows)-fallback
out['syntactic_frame_checks_pass']=True
(D/'TEMPLATES.json').write_text(json.dumps(out,separators=(',',':')));print({k:v for k,v in out.items()if k not in('records','template_keys')})
