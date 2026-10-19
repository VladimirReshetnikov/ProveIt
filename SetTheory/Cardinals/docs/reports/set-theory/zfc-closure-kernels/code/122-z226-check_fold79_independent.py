#!/usr/bin/env python3
"""All-tape proof of a 230-to-229 fold on the independently rotated K source.

Only standard library. The source-loop rewrite preceding this local fold is
separate. Every ordinary old row commutes through phi; four exceptional rows
simulate in positive blocks on open tapes. A successful result is mathematical
certificate checking, not a proof-assistant kernel theorem.
"""
from pathlib import Path
import json,hashlib,argparse

def need(p,m):
 if not p:raise ValueError(m)
def parse(p):
 t={};start=None
 for l in p.read_text().splitlines():
  if l.startswith('#! start '):need(start is None,'start repeated');start=int(l[9:])
  elif l and not l.startswith('#'):
   q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));need((q,b) not in t and b in(0,1) and w in(0,1) and d in('L','R'),'bad row');t[q,b]=(w,-1 if d=='L' else 1,z)
 states={q for q,b in t};need(set(t)=={(q,b) for q in states for b in(0,1)},'partial table');need({z for w,d,z in t.values()}-states=={254},'bad halt');need(start in states,'bad start')
 return t,start

def verify(basis,candidate):
 old,os=parse(basis);new,ns=parse(candidate);need(os==ns==0,'wrong starts')
 need(len(old)==460 and len(new)==458,'wrong sizes');need(set(q for q,b in new)==set(q for q,b in old)-{79},'deleted state')
 inv={47:{-1:1},121:{-1:1},63:{-2:1,-1:0},79:{-1:1}}
 need(os not in inv,'initial condition')
 invrows=0
 for(q,b),(w,d,z) in old.items():
  pre={**inv.get(q,{}),0:b};post={k-d:v for k,v in {**pre,0:w}.items()}
  need(all(post.get(k)==v for k,v in inv.get(z,{}).items()),f'invariant not preserved at{q}/{b}');invrows+=1
 phi=lambda q:63 if q==79 else q
 specials={(63,0),(63,1),(79,0),(79,1)}
 ordinary=0
 for(q,b),(w,d,z) in old.items():
  if(q,b) in specials:continue
  need(new[phi(q),b]==(w,d,phi(z)),f'noncommuting row{q}/{b}');ordinary+=1
 need(ordinary==456,'wrong ordinary count')
 cases=[]
 for q,b,n in[(63,0,9),(63,1,3),(79,0,3),(79,1,3)]:
  tape={**inv[q],0:b};before=dict(tape);s=phi(q);h=0;trace=[]
  for _ in range(n):
   need(s!=254,'interior halt');need(h in tape,'unbound exterior read');r=tape[h];w,d,z=new[s,r];trace.append([s,h,r,w,d,z]);tape[h]=w;s=z;h+=d
  w,d,z=old[q,b];target={**before,0:w};need((s,h,tape)==(phi(z),d,target),'bad whole-tape endpoint')
  cases.append({'old_row':[q,b],'guard':inv[q],'steps':n,'trace':trace})
 return {'status':'PASS_INDEPENDENT_ALL_TAPE_POSITIVE_BLOCK_SIMULATION','working_states_before':230,'working_states_after':229,'start':0,'halt':254,'invariant':inv,'invariant_rows':invrows,'ordinary_rows':ordinary,'cases':cases,'old_sha256':hashlib.sha256(basis.read_bytes()).hexdigest(),'new_sha256':hashlib.sha256(candidate.read_bytes()).hexdigest(),'scope':'All initial binary tapes at every integer head position. Exact whole tape at every synchronization endpoint; positive blocks with no interior halt. Source-loop transform is a separate proof.'}

def main():
 d=Path(__file__).resolve().parent;p=argparse.ArgumentParser(description=__doc__);p.add_argument('--basis',type=Path,default=d/'k230_looprotated.tm');p.add_argument('--candidate',type=Path,default=d/'k229_fold79.tm');p.add_argument('--output',type=Path,default=d/'fold79_independent.json');a=p.parse_args();r=verify(a.basis,a.candidate);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='cases'},indent=2))
if __name__=='__main__':main()
