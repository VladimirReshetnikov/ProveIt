#!/usr/bin/env python3
"""Independent finite replay and source binding; upstream code is not imported.
This is not a fresh universal primitive proof or a proof-assistant theorem.
"""
import argparse,hashlib,json,pathlib,os,sys
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
 raise RuntimeError('Assertions must be enabled; clear PYTHONOPTIMIZE and do not use -O.')
ROOT=pathlib.Path(__file__).resolve().parent
C=ROOT.parent;P=C/'parent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read_table(p):
 rows={};start=None
 for ln in p.read_text().splitlines():
  if ln.startswith('#! start '):start=int(ln.split()[-1]);continue
  if not ln or ln.startswith('#'):continue
  q,b,w,d,z=ln.split();key=int(q),int(b);assert key not in rows;assert d in('L','R');rows[key]=int(w),1 if d=='R'else-1,int(z)
 states={q for q,b in rows};assert set(rows)=={(q,b)for q in states for b in(0,1)};assert start in states;return rows,start
T,start=read_table(C/'candidate.native.tm');old,os=read_table(P/'machine/t215.native.tm');assert len(T)==430 and start==74 and os==0
changed=[(q,b,old[q,b],T[q,b])for q,b in sorted(T)if old[q,b]!=T[q,b]];assert changed==[(198,0,(1,-1,40),(0,-1,40))]
D,ds=read_table(C/'candidate.tm');mapping={int(k):v for k,v in json.loads((C/'canonicalization.json').read_text()).items()};assert ds==0 and mapping[start]==ds and mapping[254]==215
assert D=={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()}
# Tape is a zero-default dictionary and both labelled presentations are replayed.
tape={};dense={};q=start;dq=ds;h=dh=0
for tick in range(73172):
 b=tape.get(h,0);w,d,z=T[q,b]
 if w:tape[h]=1
 else:tape.pop(h,None)
 q=z;h+=d
 b=dense.get(dh,0);w,d,z=D[dq,b]
 if w:dense[dh]=1
 else:dense.pop(dh,None)
 dq=z;dh+=d
 assert mapping[q]==dq and h==dh and tape==dense
assert(q,h)==(84,-2)
# Reconstruct whole finite support independently from the claimed exact frame.
S=json.loads((C/'sites.json').read_text());assert S==json.loads((P/'machine/sites215.json').read_text())
assert S[119][0]=='11010011000110110110'
registers=[0,6,0,0,1,1,10,1,0];spares=[0,0,1]+[0]*62;physical=[None]*9
for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=registers[i]
expected={h-1,h+64}|{h+i for i,b in enumerate(S[119][0])if b=='1'};x=h+65
for value in physical+spares:
 x+=1
 for k in range(value+1):expected.add(x+k)
 x+=value+1
assert set(tape)==expected and len(tape)==107
# Full source intervals give control successors without calling upstream resolver.
paths={p:i for i,(p,op,a)in enumerate(S)};ranges={}
def interval(p):
 if p in paths:r=(paths[p],paths[p]+1)
 else:
  l=interval(p+'0');r0=interval(p+'1');assert l[1]==r0[0];r=(l[0],r0[1])
 ranges[p]=r;return r
assert interval('')==(0,len(S))
def exit_ancestor(p,edge,depth):
 for i in range(len(p)-1,-1,-1):
  if p[i]==edge:
   depth-=1
   if not depth:return ranges[p[:i]][1 if edge=='0' else 0]%len(S)
 return 0
r=[0,0,0,0,1,1,0,0,0];pc=25;transcript=[]
for _ in range(177):
 transcript.append([pc,list(r)]);p,op,a=S[pc]
 if op=='CI':r[a]+=1;pc=(pc+1)%len(S)
 elif op=='CD':
  if r[a]:r[a]-=1;pc=(pc+1)%len(S)
  else:pc=exit_ancestor(p,'0',1)
 elif op in('CB','CC'):pc=exit_ancestor(p,'0'if op=='CB'else'1',a)
 else:raise AssertionError('AX prefix must not halt')
assert pc==119 and r==registers
# AX ordinal25 subtree and compiler binding remain byte-for-byte inherited.
assert len(S)==4775 and all(x==y for x,y in zip(S,json.loads((P/'machine/sites215.json').read_text())))
out={'status':'INDEPENDENT_FINITE_REPLAY_SOURCE_BINDING_PASS','table_sha256':sha(C/'candidate.native.tm'),'source_sha256':sha(C/'sites.json'),'dense_sha256':sha(C/'candidate.tm'),'states':215,'rows':430,'changed_rows_from_public_MP_first':changed,'start_change':[os,start],'blank_transitions':73172,'dispatcher':q,'head':h,'header':62,'gap':0,'ordinal':pc,'source_address':S[pc][0],'logical_registers':r,'spares':spares,'complete_one_cells':sorted(tape),'source_prefix_entry':25,'source_prefix_seed':[0,0,0,0,1,1,0,0,0],'source_prefix_steps':177,'source_prefix_trace_sha256':hashlib.sha256(json.dumps(transcript,separators=(',',':')).encode()).hexdigest(),'scope':'Own tape and interval-CFG implementations, exact source equality, canonical relabeling, full finite blank support and 177-step logical AX match. Does not reprove universal runtime or inherited numerical-calculus/ZFC calibration.'}
args=argparse.ArgumentParser();args.add_argument('--out',type=pathlib.Path);opts=args.parse_args()
if opts.out:opts.out.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k not in('spares','complete_one_cells')},indent=2))
