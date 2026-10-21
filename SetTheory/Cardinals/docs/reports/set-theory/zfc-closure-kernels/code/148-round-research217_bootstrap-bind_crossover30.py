#!/usr/bin/env python3
"""Owned literal fresh startup/prefix binding for the closed 30-leaf rotation."""
from pathlib import Path
import collections,hashlib,json,time
ROOT=Path(__file__).resolve().parents[1];D=ROOT/'research217_bootstrap/crossover30'
P=ROOT/'research217_encoding/crossover30_primary/raw218.native.tm';F=ROOT/'research217_encoding/crossover30_primary/sites.json'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P)=='a014d72c9052dd5fa56082a436ca3b16ce559f3491c2c0d74e33cb389eb98f06'
assert H(F)=='a2c2620f637905eca0126ba73fd59861ccc5e9621813dc582d7e719e44bb7c51'
def table(p):
 T={}
 for l in p.read_text().splitlines():
  if l and not l.startswith('#'):
   q,b,w,d,n=l.split();T[int(q),int(b)]=int(w),1 if d=='R'else -1,int(n)
 return T
T=table(P);C=T.copy()
assert [C[k]for k in[(87,0),(88,0),(51,0),(301,0),(301,1)]]==[(0,1,301),(0,1,122),(0,1,16),(0,1,45),(1,1,103)]
C={k:v for k,v in C.items()if k[0]!=301};C.update({(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122)})
CP=D/'initialized217.native.tm';CP.write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'for(q,b),(w,d,n)in sorted(C.items())))
assert len(C)==434
PHY=(6,2,0,4,3,7,8,5,1)
def cleanroot(q,h,ones):
 if q!=84 or not ones or min(ones)!=h-1:return None
 rest=sorted(ones-{h-1})
 if not rest or rest[0]<h+40:return None
 header=rest[0];p=header+1;v=[];last=rest[-1]
 while p<=last:
  if p in ones or p+1 not in ones:return None
  s=p+1;p=s
  while p in ones:p+=1
  v.append(p-s-1)
 if len(v)<10 or p!=last+1:return None
 return dict(registers=[v[j]for j in PHY],header_distance=header-h,gap40=header-h-40,spares=v[9:])
ones=set();q=h=0;boot=[];all51=0;started=time.monotonic();cap=1_000_000
for tick in range(cap+1):
 root=cleanroot(q,h,ones)
 if root is not None:status='FIRST_CLEAN_ROOT_REACHED';break
 if q==254:status='HALTED';break
 if tick==cap:status='CAP_REACHED_NOT_A_NONHALTING_PROOF';break
 b=int(h in ones)
 if q==51 and b==0:
  all51+=1
  if h+1 not in ones:boot.append(dict(step=tick,head=h,relative_ones=sorted(p-h for p in ones),left6=sum(1<<i for i in range(6)if h-6+i in ones)))
 w,d,q=T[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
end=dict(step=tick,state=q,head=h,one_cells=sorted(ones),clean=root)
decoder=[];outcomes=collections.Counter();maxread=-100
for i,site in enumerate(json.loads(F.read_text())):
 pc,op,arg=site;cells={-1}|{j for j,b in enumerate(pc)if b=='1'};q=84;h=0;seen=set();trace=[]
 for tick in range(200):
  if h>=40:stop='HEADER_OR_GAP_FRONTIER';break
  if(q,h)in seen:stop='READ_ONLY_EXACT_CYCLE';break
  if q==254:stop='HALT';break
  seen.add((q,h));maxread=max(maxread,h);b=int(h in cells)
  if q==51 and b==0 and h+1 not in cells:decoder.append(dict(source_index=i,site=site,tick=tick,head=h,left6=sum(1<<j for j in range(6)if h-6+j in cells),trace=trace.copy()))
  w,d,n=C[q,b];trace.append([q,h,b,w,d,n])
  if w!=b:stop='FIRST_DESTRUCTIVE_STEP';break
  q,h=n,h+d
 else:stop='PREFIX_BOUND'
 outcomes[stop]+=1
boot_masks=sorted({e['left6']for e in boot});decoder_masks=sorted({e['left6']for e in decoder})
separation=[dict(depth=k,boot=sorted({m>>(6-k)for m in boot_masks}),decoder=sorted({m>>(6-k)for m in decoder_masks}),disjoint=not {m>>(6-k)for m in boot_masks}&{m>>(6-k)for m in decoder_masks})for k in range(1,7)]
out=dict(status=status,parent_sha256=H(P),source_sha256=H(F),composed_sha256=H(CP),blank_cap=cap,blank_endpoint=end,boot_q51_read0_visits=all51,boot_exceptions=boot,decoder_prefix_events=decoder,boot_left6=boot_masks,decoder_left6=decoder_masks,depth_separation=separation,prefix_outcomes=dict(outcomes),max_read_head=maxread,seconds=time.monotonic()-started,scope='Fresh exact finite blank initialization of the crossover218 table, plus all source read-only prefixes of its folded217. No claim yet about later symbolic primitive contexts or a four-bit physical classifier.')
(D/'CONTEXT_BINDING.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k not in('blank_endpoint','boot_exceptions','decoder_prefix_events')},indent=2));print('endpoint',{k:v for k,v in end.items()if k!='one_cells'});print('boot steps',[e['step']for e in boot])
