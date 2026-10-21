#!/usr/bin/env python3
"""Independent source, relabeling, and complete-tape startup audit of K217.

Uses no delivered source parser, CFG resolver, simulator, or frame decoder.
All source and machine input identities are explicit and hash checked.
"""
from pathlib import Path
import argparse, hashlib, json
if not __debug__:
 raise RuntimeError('Verification requires assertions; do not use -O or PYTHONOPTIMIZE.')

PINS={
 'baseline218.native.tm':'9c8505bf3731212192b83ee61dbc569085b4675ae9e0539843ae57d43ad9e886',
 'baseline_sites218.json':'264fba90229974a53c2c5c943cf5fe8924327b6bbc31bd47e64d7f5c670b7495',
 'prefold218.native.tm':'34617022def75d88a4f357589d7a48f468d17b58c910947ed0738aa3c6a5760a',
 'k217.native.tm':'c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099',
 'k217.tm':'a2b8bc2d4822962ad32819fe475a7d62b0d483bc4f41977bff292742f70b3e8c',
 'sites217.json':'9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655',
}
PHY=(6,2,0,4,3,7,8,5,1)
PREFIX='11101001001110010'

def digest(raw):return hashlib.sha256(raw).hexdigest()
def table(raw,halt):
 d={};starts=[]
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '):starts.append(int(line.split()[-1]))
  elif line and not line.startswith('#'):
   q,b,w,di,z=line.split();q,b,w,z=map(int,(q,b,w,z))
   assert (q,b)not in d and b in(0,1)and w in(0,1)and di in('L','R')
   d[q,b]=(w,1 if di=='R'else-1,z)
 states={q for q,b in d}
 assert starts==[0]and set(d)=={(q,b)for q in states for b in(0,1)}
 assert {z for w,di,z in d.values()}-states=={halt}
 return d

def ast(rows):
 instructions={p:(o,r)for p,o,r in rows};assert len(instructions)==len(rows)
 prefixes={p[:k]for p in instructions for k in range(len(p))};assert not prefixes&instructions.keys()
 assert all(p+'0'in prefixes|instructions.keys()and p+'1'in prefixes|instructions.keys()for p in prefixes)
 def rec(p=''):
  if p in instructions:return instructions[p]
  return rec(p+'0'),rec(p+'1')
 return rec()

def leaf(q):return isinstance(q[0],str)
def flat(q,p=''):
 return [[p,*q]]if leaf(q)else flat(q[0],p+'0')+flat(q[1],p+'1')
def sub(q,p):
 for c in p:q=q[int(c)]
 return q
def boundary(q):
 if leaf(q):
  o,r=q;return (1,0,False)if o=='CD'else(r,0,False)if o=='CB'else(0,r,False)if o=='CC'else(0,0,o=='CH')
 a,b=map(boundary,q);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2]
def intern_count(q):
 seen=set()
 def go(n):
  if n in seen:return
  seen.add(n)
  if not leaf(n):go(n[0]);go(n[1])
 go(q);return len(seen)

def control_graph(q):
 """Resolve targets using explicit stacks of enclosing loop/exit labels."""
 rr=flat(q);indices={p:i for i,(p,o,r)in enumerate(rr)};total=len(rr);out=[]
 def rec(n,p,start,breaks,continues):
  if leaf(n):
   o,r=n;nxt=(start+1)%total
   if o=='CI':ts=[nxt]
   elif o=='CD':ts=[breaks[0]if breaks else 0,nxt]
   elif o=='CB':ts=[breaks[r-1]if r<=len(breaks)else 0]
   elif o=='CC':ts=[continues[r-1]if r<=len(continues)else 0]
   else:assert o=='CH';ts=[]
   out.append([o,r,ts]);assert indices[p]==start
   return start+1
  leftlen=len(flat(n[0]));end=start+len(flat(n));mid=start+leftlen
  x=rec(n[0],p+'0',start,[end%total]+breaks,continues);assert x==mid
  y=rec(n[1],p+'1',mid,breaks,[start]+continues);assert y==end
  return end
 rec(q,'',0,[],[]);assert len(out)==total;return out

def expected_tape():
 logical=[3,0,0,0,3,0,0,0,0];phys=[0]*9
 for i,j in enumerate(PHY):phys[j]=logical[i]
 head=-5;header=head+64+80;ones={head-1,header};p=header+1
 for v in phys+[1]*130:
  ones.update(range(p+1,p+v+2));p+=v+2
 assert len(ones)==277
 return ones

def run_dense(T,steps,expected_state):
 """Fixed finite tape bounds are checked on every step, never assumed."""
 lo=-8192;hi=8192;tape=bytearray(hi-lo+1);q=0;h=0;used=set();minh=maxh=0;tr=hashlib.sha256()
 for tick in range(steps):
  assert lo<=h<=hi and (q,tape[h-lo])in T,('early halt or tape bound',tick,q,h)
  b=tape[h-lo];w,d,z=T[q,b];used.add((q,b));tr.update(f'{q},{h},{b},{w},{d},{z};'.encode())
  tape[h-lo]=w;q=z;h+=d;minh=min(minh,h);maxh=max(maxh,h)
 actual={i+lo for i,b in enumerate(tape)if b}
 assert q==expected_state and h==-5 and actual==expected_tape(),('wrong full endpoint',q,h,len(actual))
 return dict(steps=steps,state=q,head=h,one_cells=sorted(actual),one_cells_count=len(actual),minimum_head=minh,maximum_head=maxh,used_rows=sorted(used),trace_sha256=tr.hexdigest(),zero_exterior=True)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 raw={n:(a.input/n).read_bytes()for n in PINS}
 assert all(digest(raw[n])==h for n,h in PINS.items()),'input hash mismatch'
 old=table(raw['baseline218.native.tm'],254);pre=table(raw['prefold218.native.tm'],254);new=table(raw['k217.native.tm'],254);dense=table(raw['k217.tm'],217)
 oldrows=json.loads(raw['baseline_sites218.json']);rows=json.loads(raw['sites217.json']);ot=ast(oldrows);nt=ast(rows)
 assert flat(ot)==oldrows and flat(nt)==rows
 O=sub(ot,PREFIX);A=O[0];(((B,C),D),E)=O[1]
 assert sub(nt,PREFIX)==((A,B),((C,D),E))
 lens=list(map(lambda n:len(flat(n)),[A,B,C,D,E]));assert lens==[14,27,53,374,3682]
 assert all(boundary(n)==(0,0,False)for n in[A,B,C,D,E])
 assert [r[1:]for r in oldrows]==[r[1:]for r in rows]
 og=control_graph(ot);ng=control_graph(nt);assert og==ng
 changed=[i for i,(x,y)in enumerate(zip(oldrows,rows))if x!=y];assert changed==list(range(187,281))
 assert intern_count(ot)==intern_count(nt)==203
 assert len(rows)==4751 and max(map(lambda x:len(x[0]),rows))==45
 assert max(len(s)for p,_,_ in rows for s in p.split('1'))==6
 expected_patch={(201,0):(0,1,188),(188,0):(0,1,92),(188,1):(1,1,90),(210,0):(0,1,146)}
 assert {k:v for k,v in pre.items()if old[k]!=v}==expected_patch and set(pre)==set(old)
 expected_new={(q,b):(w,d,69 if z==400 else z)for(q,b),(w,d,z)in pre.items()if q!=400}
 expected_new[69,0]=(0,-1,188);assert new==expected_new
 states=sorted({q for q,b in new});assert len(states)==217 and len(new)==434
 bfs=[0];seen={0}
 for q in bfs:
  for bit in(0,1):
   z=new[q,bit][2]
   if z!=254 and z not in seen:seen.add(z);bfs.append(z)
 mp={q:i for i,q in enumerate(bfs)};mp[254]=217
 assert {(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in new.items()}==dense
 reach={0};todo=[0]
 for q in todo:
  for b in(0,1):
   z=new[q,b][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 assert reach==set(states)
 boot=run_dense(new,312617,84);canonical=run_dense(dense,312617,mp[84]);baseline=run_dense(old,312605,84);prefold=run_dense(pre,312605,84)
 # Every pre-fold source-layout edit is absent from the complete old boot.
 assert not set(expected_patch)&{tuple(x)for x in baseline['used_rows']}
 assert baseline['trace_sha256']==prefold['trace_sha256']
 for label in(69,400):
  inc=[(k,v)for k,v in pre.items()if v[2]==label]
  assert inc==[(((53,1)if label==69 else(224,0)),((1,1,69)if label==69 else(0,1,400)))]
 report=dict(status='INDEPENDENT_SOURCE_RELABELING_FULL_STARTUP_PASS',pins=PINS,working_states=217,rows=434,graph_reachable_states=217,source_leaves=4751,source_dag_nodes=203,guarded_cases=sum(2 if o=='CD'else 1 for p,o,r in rows),changed_source_ordinals=[187,280],changed_source_addresses=94,closed_component_lengths=lens,guarded_cfg_equal=True,source_cfg_sha256=digest(json.dumps(ng,separators=(',',':')).encode()),prefold_patch_preserves_every_startup_row=True,boot=boot,canonical_boot={k:v for k,v in canonical.items()if k not in('one_cells','used_rows')},baseline_boot={k:v for k,v in baseline.items()if k not in('one_cells','used_rows')},scope='Independent exact finite construction/CFG/startup audit; general runtime and consistency calibration remain separate proof components.')
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k not in('boot','canonical_boot','baseline_boot','pins')},indent=2))

if __name__=='__main__':main()
