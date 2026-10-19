#!/usr/bin/env python3
"""Independently check the four guarded open-tape identities for K229 -> K228.

The extra right-one guard at old169/read1 must be supplied by the separate
unbounded runtime certificate and the exact blank-startup certificate.
This checker proves the other guards inductively from every initial tape.
"""
from pathlib import Path
import argparse,hashlib,json

OLD_SHA='b96eeef7cfd5083f3ab737fa7885482ebcae2a947bce5fb20e54a547dc254d32'
NEW_SHA='7f5153ac9360cbab06a4c8ce0a01d55228a4f4e32dcd83a3234d5ef94c2f35a6'
FACTS={67:{-1:0},80:{-2:0,-1:1},91:{-3:0,-2:1,-1:1},169:{-1:0}}
SPECS=[(80,0,{-1:1},5),(169,0,{-1:0},3),(169,1,{-1:0,1:1},5),(91,1,{-3:0,-2:1,-1:1},9)]
def require(ok,msg):
 if not ok:raise ValueError(msg)
def read(path):
 raw=Path(path).read_bytes();t={};start=None
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '):require(start is None,'duplicate header');start=int(line[9:])
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));require(b in(0,1)and w in(0,1)and d in('L','R'),'malformed row');require((q,b)not in t,'duplicate row');t[q,b]=(w,1 if d=='R'else-1,z)
 qs={q for q,b in t};require(set(t)=={(q,b)for q in qs for b in(0,1)},'partial table');require({z for w,d,z in t.values()}-qs=={254},'halt');require(start==95,'start')
 return t,hashlib.sha256(raw).hexdigest()
def phi(q):return 80 if q==169 else q
def block(t,q,guard,n):
 h=0;delta={};trace=[]
 def original(p):return guard.get(p,('arbitrary_exterior_cell',p))
 for tick in range(n):
  b=delta.get(h,original(h));require(type(b)is int and b in(0,1),f'unresolved read:{q},{h}');require(q!=254,'interior halt')
  w,d,z=t[q,b];trace.append([q,h,b,w,d,z])
  if w==original(h):delta.pop(h,None)
  else:delta[h]=w
  q,h=z,h+d
 return q,h,delta,trace
def verify(oldpath,newpath):
 old,oh=read(oldpath);new,nh=read(newpath);require(oh==OLD_SHA and nh==NEW_SHA,'unexpected input bytes');require(len(old)==458 and len(new)==456,'counts')
 wanted={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=169};wanted[80,0]=(0,-1,106);wanted[91,1]=(1,-1,167);require(new==wanted,'unexpected edit')
 require(95 not in FACTS,'initial invariant')
 invchecks=0
 for(q,b),(w,d,z)in old.items():
  known={**FACTS.get(q,{}),0:b}
  if FACTS.get(q,{}).get(0,b)!=b:continue
  known[0]=w
  require(all(known.get(d+k)==v for k,v in FACTS.get(z,{}).items()),f'invariant not inductive:{q},{b}');invchecks+=1
 incoming={q:[[p,b,w,d]for(p,b),(w,d,z)in sorted(old.items())if z==q]for q in FACTS}
 special={(q,b)for q,b,g,n in SPECS};records=[]
 for q,b,g,n in SPECS:
  guard={**g,0:b};oq,ohh,ot,otr=block(old,q,guard,1);nq,nhh,nt,ntr=block(new,phi(q),guard,n)
  require((phi(oq),ohh,ot)==(nq,nhh,nt),f'block mismatch:{q},{b}')
  records.append(dict(old_row=[q,b],guard=guard,old_steps=1,new_steps=n,old_trace=otr,new_trace=ntr,endpoint=[nq,nhh,nt],arbitrary_exterior_unread=True))
 ordinary=0
 for(q,b),(w,d,z)in old.items():
  if(q,b)not in special:require(new[phi(q),b]==(w,d,phi(z)),f'ordinary mismatch:{q},{b}');ordinary+=1
 require(ordinary==454,'ordinary count')
 return dict(status='PASS_EXACT_GUARDED_LOCAL_IDENTITIES',old_sha256=OLD_SHA,new_sha256=NEW_SHA,old_states=229,new_states=228,inductive_bit_facts=FACTS,inductive_rows_checked=invchecks,incoming=incoming,ordinary_rows=ordinary,blocks=records,extra_runtime_guard='Every old169/read1 entry has tape(head+1)=1. This assertion is NOT proved here.',clock='tau(t)=t+4*V80,0(t)+2*V169,0(t)+4*V169,1(t)+8*V91,1(t)',scope='Universal infinite-tape local identities under the stated guards, plus all-tape inductivity of every guard except the explicitly external right-one runtime guard.')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--old',type=Path,required=True);p.add_argument('--new',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=verify(a.old,a.new);r['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items()if k not in('blocks','incoming')},indent=2))
