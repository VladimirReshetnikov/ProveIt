"""Owned fresh sparse-native and dense-canonical blank bootstrap; inert data only."""
from pathlib import Path
from collections import deque,Counter
import hashlib,json,time
D=Path(__file__).resolve().parent;ROOT=D.parent;P=ROOT/'research217_review/contextual/selected/machine';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,m,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert m in('L','R')and b in(0,1)and w in(0,1)and(q,b)not in t;t[q,b]=(w,m,z)
 Q={q for q,b in t};assert all((q,b)in t for q in Q for b in(0,1))and len(t)==2*len(Q)
 return t
N=table(P/'k218.native.tm');C=table(P/'k218.tm');old=table(ROOT/'latest219_baseline/candidate-k219/k219.native.tm')
assert H(P/'k218.native.tm')=='3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1'and H(P/'k218.tm')=='7ca993f2c7f2cbdbca5b69756712d0fac17ff81e81e260190a599115c0643acb'
assert len(N)==len(C)==436
mp={0:0};todo=deque([0])
while todo:
 q=todo.popleft()
 for b in(0,1):
  z=N[q,b][2]
  if z!=254 and z not in mp:mp[z]=len(mp);todo.append(z)
assert len(mp)==218;mp[254]=218
assert mp[84]==23 and {(mp[q],b):(w,m,mp[z])for(q,b),(w,m,z)in N.items()}==C
normalized=table(P/'k218.normalized.tm');norm=lambda q:{301:102,302:120}.get(q,q)
assert {(norm(q),b):(w,m,norm(z))for(q,b),(w,m,z)in N.items()}==normalized
received=json.loads((P.parent/'certificates/runtime/startup.json').read_text())
assert {norm(q):z for q,z in mp.items()}=={int(k):int(v)for k,v in received['normalized_to_canonical'].items()}
assert H(P/'k218.normalized.tm')=='4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651'
assert H(P/'sites218.json')=='1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe'
removed=sorted(set(old)-set(N));added=sorted(set(N)-set(old));changes=[dict(row=k,old=old[k],new=N[k])for k in sorted(set(old)&set(N))if old[k]!=N[k]]
assert len(N)==436 and len(old)==438
PHY=(6,2,0,4,3,7,8,5,1)
def parse(h,ones):
 if h-1 not in ones or any(x<h-1 for x in ones):return None
 right=sorted(x for x in ones if x>=h+64)
 if not right:return None
 header=right[0];addr=sorted(x-h for x in ones if h<=x<header)
 if any(x>=38 for x in addr):return None
 pos=header+1;end=max(ones);values=[]
 while pos<end:
  if pos in ones or pos+1 not in ones:return None
  start=pos+1;pos=start
  while pos in ones:pos+=1
  values.append(pos-start-1)
 if pos!=end+1 or len(values)<10:return None
 return dict(header=header,extra_gap=header-h-64,address_one_positions=addr,root_address=(not addr),logical=[values[i]for i in PHY],physical=values[:9],spares=values[9:])
def build(h,logical,gap,spares):
 phys=[0]*9
 for j,i in enumerate(PHY):phys[i]=logical[j]
 header=h+64+gap;ones={h-1,header};pos=header+1
 for n in phys+spares:
  pos+=1;ones.update(range(pos,pos+n+1));pos+=n+1
 return ones
EXPECTED=build(-5,[3,0,0,0,3,0,0,0,0],80,[1]*130);assert len(EXPECTED)==277
# Sparse execution and full clean-frame inspection at every dispatcher visit.
q=head=0;ones=set();frames=[];root_frames=[];checkpoints={};raw_dispatches=0;visited={0};counts=Counter();began=time.monotonic()
for tick in range(312701+1):
 assert q!=254
 if q==84:
  raw_dispatches+=1;f=parse(head,ones)
  if f:
   rec=dict(steps=tick,state=q,head=head,one_cells=sorted(ones),**f);frames.append(rec)
   if f['root_address']:root_frames.append(rec)
 if (len(frames)==1 and frames[0]['steps']==tick) or tick==312701:checkpoints[tick]=dict(state=q,head=head,one_cells=sorted(ones))
 if tick==312701:break
 b=int(head in ones);counts[q,b]+=1;w,m,q=N[q,b]
 if w:ones.add(head)
 else:ones.discard(head)
 head+=1 if m=='R'else -1;visited.add(head)
assert(q,head,ones)==(84,-5,EXPECTED)
assert root_frames and root_frames[0]['steps']==312701
assert frames and not frames[0]['root_address']
assert sorted((norm(q),b,n)for(q,b),n in counts.items())==sorted(map(tuple,received['startup_row_counts']))
# Independently written dense representation and canonical labels. Each side
# grows with zero cells. Unrepresented exterior remains zero by construction.
left=bytearray();right=bytearray(1);q=0;pos=0;densechecks=[];dense_root=[];dense_clean=[];densecounts=Counter()
for tick in range(312701+1):
 assert q!=218
 if q==23 or tick in checkpoints:
  support={i for i,b in enumerate(right)if b}|{-i-1 for i,b in enumerate(left)if b}
  if q==23:
   f=parse(pos,support)
   if f:
    dense_clean.append(tick)
    if f['root_address']:dense_root.append(tick)
  if tick in checkpoints:
   ref=checkpoints[tick];assert(q,pos,support)==(mp[ref['state']],ref['head'],set(ref['one_cells']));densechecks.append(tick)
 if tick==312701:break
 buf,off=(right,pos)if pos>=0 else(left,-pos-1)
 if off>=len(buf):buf.extend(b'\0'*(off+1-len(buf)))
 densecounts[q,buf[off]]+=1;w,d,z=C[q,buf[off]];buf[off]=w;q=z;pos+=(1 if d=='R'else -1)
assert dense_clean==[x['steps']for x in frames]and dense_root==[x['steps']for x in root_frames]
assert(q,pos,support)==(23,-5,EXPECTED)
assert densecounts==Counter({(mp[q],b):n for(q,b),n in counts.items()})
result=dict(status='INDEPENDENT_SPARSE_NATIVE_AND_DENSE_CANONICAL_BOOT_PASS',native_sha256=H(P/'k218.native.tm'),canonical_sha256=H(P/'k218.tm'),source_sha256=H(P/'sites218.json'),states=218,rows=436,normalized_sha256=H(P/'k218.normalized.tm'),normalized_isomorphism=True,all_transition_counts_sparse_dense_equal=True,startup_row_counts=[[q,b,n]for(q,b),n in sorted(counts.items())],removed_rows=removed,added_rows=added,changed_retained_rows=changes,bfs_isomorphism=True,all_graph_reachable=True,halt_excluded=True,steps=312701,first_clean_dispatch=frames[0]['steps'],first_clean_dispatch_is_not_root=True,first_clean_root_dispatch=312701,raw_dispatch_visits=raw_dispatches,clean_dispatches=len(frames),root_dispatches=len(root_frames),native_state=84,canonical_state=23,head=-5,header=139,extra_gap=80,logical=[3,0,0,0,3,0,0,0,0],spare_count=130,spare_value=1,one_count=277,one_cells=sorted(EXPECTED),all_other_cells_zero=True,no_earlier_halt=True,dense_full_support_checkpoints=densechecks,visited_head_range=[min(visited),max(visited)],seconds=time.monotonic()-began,driver_sha256=H(Path(__file__)))
(D/'BOOT_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');(D/'CLEAN_BOOT_FRAMES.json').write_text(json.dumps(frames,indent=2)+'\n');(D/'CANONICAL_MAP.json').write_text(json.dumps(mp,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('one_cells','changed_retained_rows')},indent=2))
