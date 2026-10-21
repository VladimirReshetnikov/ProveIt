#!/usr/bin/env python3
"""Finite certificate prototype, NOT a Lean/Rocq proof.

A generic kernel locality and positive-stuttering theorem would turn these
finite checks into an exact endpoint transport. Only stdlib is required.
"""
from pathlib import Path
from collections import deque
import argparse,hashlib,json,sys
D=Path(__file__).resolve().parent
PINS={'reference.tm':'9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2','candidate.tm':'e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252'}
def parse(p):
 raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==PINS[p.name]
 table={};start=None
 for line in raw.decode().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1])
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert d in ('L','R') and b in (0,1) and w in (0,1)
  assert (q,b)not in table;table[q,b]=(w,1 if d=='R'else -1,z)
 states={q for q,b in table};assert len(states)==215 and len(table)==430 and start==0
 assert set(table)=={(q,b)for q in states for b in(0,1)}
 assert {z for w,d,z in table.values()}-states=={254}
 return table,states

def successor_window(bits,w,d,exterior):
 # low bit is the left neighbor, middle is the scanned symbol.
 l,c,r=(bits>>j&1 for j in range(3))
 return (w+2*r+4*exterior) if d==1 else(exterior+2*l+4*w)

def synthesize(t,states,blank=False):
 masks={q:0 for q in states|{254}};queue=deque()
 for bits in ([0]if blank else range(8)):masks[0]|=1<<bits;queue.append((0,bits))
 while queue:
  q,bits=queue.popleft()
  if q==254:continue
  w,d,z=t[q,(bits>>1)&1]
  for e in (0,1):
   b=successor_window(bits,w,d,e)
   if not(masks[z]>>b&1):masks[z]|=1<<b;queue.append((z,b))
 return masks

def step(t,q,h,ones):
 assert -2<=h<=2,'Read escaped certified finite window'
 w,d,z=t[q,int(h in ones)];out=set(ones)
 if w:out.add(h)
 else:out.discard(h)
 return z,h+d,out

def verify(t,u,states,mask,all_initial=True):
 assert set(mask)==states|{254}
 assert all(0<=v<256 for v in mask.values())
 assert mask[0]==255 if all_initial else mask[0]&1
 phi=lambda q:52 if q==176 else q
 assert phi(0)==0 and phi(254)==254 and all(phi(q)!=254 for q in states)
 assert all(phi(q)in states for q in states)
 closure=blocks=0;by_length={1:0,3:0}
 for q in sorted(states):
  for window in range(32):
   oldbits=(window>>1)&7
   if not(mask[q]>>oldbits&1):continue
   ones={j-2 for j in range(5)if window>>j&1}
   z,h,out=step(t,q,0,ones)
   newbits=sum(int(h+j in out)<<(j+1)for j in (-1,0,1))
   assert mask[z]>>newbits&1,('closure',q,window,z,newbits)
   closure+=1
   k=3 if q in (52,176)and not(window>>2&1)else 1
   cq,ch,co=phi(q),0,set(ones)
   for _ in range(k):
    assert cq!=254,'Premature halt inside a block'
    cq,ch,co=step(u,cq,ch,co)
   assert(cq,ch,co)==(phi(z),h,out),('simulation',q,window,k)
   blocks+=1;by_length[k]+=1
 return {'closure_cases':closure,'block_cases':blocks,'block_lengths':by_length,'maximum_read_radius':2,'positive_block_lengths':True,'halt_preservation':True,'halt_reflection':True,'whole_window_and_head_equal':True}

def main():
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path);p.add_argument('--certificate',type=Path);a=p.parse_args()
 t,s=parse(D/'inputs/reference.tm');u,s2=parse(D/'inputs/candidate.tm');assert s==s2
 manual={q:255 for q in s|{254}};manual[52]=170;manual[156]=240;manual[176]=221
 if a.certificate:
  cert_in=json.loads(a.certificate.read_text())
  assert cert_in['schema']==1 and cert_in['table_sha256']==PINS
  assert cert_in['working_states']==sorted(s) and cert_in['halt']==254 and cert_in['start']==0
  assert cert_in['state_map_exception']=={'176':52}
  assert cert_in['invariant_radius']==1 and cert_in['read_window_radius']==2
  assert cert_in['block_length_rule']=='3 iff old control is52 or176 and old read is0; otherwise1'
  manual={int(q):v for q,v in cert_in['invariant_masks'].items()}
 strong=synthesize(t,s);blank=synthesize(t,s,True)
 results={name:verify(t,u,s,m,all_initial=initial)for name,m,initial in [('three_clause',manual,True),('synthesized_arbitrary_tape',strong,True),('synthesized_blank',blank,False)]}
 # Independently state the human-readable three clauses for all8 triples.
 for bits in range(8):
  l,c,r=(bits>>j&1 for j in range(3))
  assert bool(manual[52]>>bits&1)==bool(l)
  assert bool(manual[156]>>bits&1)==bool(r)
  assert bool(manual[176]>>bits&1)==bool(c or not l)
 cert={'schema':1,'state_map_exception':{'176':52},'working_states':sorted(s),'halt':254,'start':0,'invariant_radius':1,'read_window_radius':2,'invariant_masks':{str(q):manual[q]for q in sorted(manual)},'table_sha256':PINS,'block_length_rule':'3 iff old control is52 or176 and old read is0; otherwise1'}
 report={'status':'FINITE_TRANSPORT_OBLIGATIONS_PASS','kernel_checked':False,'results':results,'synthesized_masks_of_interest':{str(q):strong[q]for q in(52,156,176)},'abstract_reachable_working_states':{'arbitrary_initial_tape':sum(bool(strong[q])for q in s),'blank_initial_window':sum(bool(blank[q])for q in s)},'source_count_claim':None,'scope':'Exact finite window checks and inductive abstract invariant. A generic theorem connecting window locality and positive stuttering to concrete Lean/Rocq semantics is still required; this script is not a new kernel-checked endpoint.'}
 if a.out:
  a.out.mkdir(parents=True,exist_ok=True);(a.out/'certificate.json').write_text(json.dumps(cert,indent=2)+'\n');(a.out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()
