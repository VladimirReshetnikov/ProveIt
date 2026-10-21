from pathlib import Path
import sys,json,itertools,hashlib,time,functools
F=Path(__file__).resolve().parent;O=F.parent/'reproduced/prefix-codes';O.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(F));import complement_quantifier as c
s,m=c.s,c.m;c.spans['GEN']=(40,121);inc=c.inc
@functools.lru_cache(None)
def shapes(n):
 if n==1:return (None,)
 return tuple((a,b)for k in range(1,n)for a in shapes(k)for b in shapes(n-k))
def leaves(t,p=''):
 if t is None:return [p]
 return leaves(t[0],p+'0')+leaves(t[1],p+'1')
@functools.lru_cache(None)
def constant(n,style,reg=1):
 if n==1:return ('CI',reg)
 if style=='left-power':a=1<<(n.bit_length()-1);a=a//2 if a==n else a
 elif style=='right-power':a=n-(1<<(n.bit_length()-1));a=n//2 if a==0 else a
 else:a=n//2
 return constant(a,style,reg),constant(n-a,style,reg)
def scaled(scale,style):return c.imp[0],(c.imp[1][0],(('CD',7),(constant(scale,style),('CC',2))))
nip=s.subtree(c.tree,'110100101');parity=(('CD',5),((('CD',5),('CC',2)),('CH',None)))
results=[];seen=set();best=999;begin=time.time()
for shapeid,shape in enumerate(shapes(4)):
 ps=leaves(shape)
 for perm in itertools.permutations('IRQE'):
  codes={tok:(2**len(p),sum(int(bit)*2**i for i,bit in enumerate(p)))for tok,p in zip(perm,ps)}
  if codes['R'][1]==0:continue
  for style,placement in itertools.product(['left-power','right-power','balanced'],['after','before-final-loop']):
   mac=dict(c.mac)
   for tok,(scale,off)in codes.items():
    core=scaled(scale,style)
    if off:
     tag=constant(off,style)
     if placement=='after':core=(core,tag)
     else:core=(core[0],(core[1][0],(tag,core[1][1])))
    mac[tok]=core
   mac['F']=(c.push,constant(codes['R'][1],style))
   for haltmode in ['exact']+(['parity']if codes['R']==(2,1)else[]):
    newnip=(constant(codes['R'][1],style,6),nip[1]) if haltmode=='exact' else (parity,nip[1][1])
    sig=tuple(mac[k]for k in 'IRQEF')+(newnip,)
    if sig in seen:continue
    seen.add(sig);patches=[]
    for name,(lo,hi)in c.spans.items():
     offset=lo
     for tok in c.postfix(c.forms[name]):
      n=len(m.flat(c.mac[tok]));new=mac[tok]
      if new!=c.mac[tok]:patches.append((offset,offset+n,new))
      offset+=n
     assert offset==hi
    if mac['I']!=c.imp:
     patches.append((4678,4705,mac['I']))
     patches.extend((i,i+27,mac['I'])for i in [194,247,326,405,432,459])
    rr=c.tree
    for lo,hi,new in sorted((p for p in patches if p[0]>4598),reverse=True):rr=m.splice(s,rr,lo,hi,new)
    if newnip!=nip:rr=s.replace(rr,'110100101',newnip)
    for lo,hi,new in sorted((p for p in patches if p[0]<4598),reverse=True):rr=m.splice(s,rr,lo,hi,new)
    met=s.metrics(rr);no=len(results);raw=s.compact(s.sites(rr));rec={'id':no,'shape':shapeid,'paths':ps,'codes':codes,'constant_style':style,'placement':placement,'haltmode':haltmode,'metrics':met,'source_sha256':hashlib.sha256(raw).hexdigest()};results.append(rec)
    if met['dag_nodes']<=212:(O/(f'prefix-{no}.sites.json')).write_bytes(raw)
    if met['dag_nodes']<best:best=met['dag_nodes'];print('BEST',rec,flush=True);(O/'best.sites.json').write_bytes(raw)
    if no%50==0:
     print('progress',no,'seconds',time.time()-begin,flush=True)
     (O/'progress.json').write_text(json.dumps(results)+'\n')
    m.flat.cache_clear();s.boundary.cache_clear()
(O/'results.json').write_text(json.dumps(results,indent=2)+'\n');print('DONE',len(results),'best',best,'seconds',time.time()-begin,flush=True)
