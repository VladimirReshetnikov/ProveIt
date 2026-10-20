#!/usr/bin/env python3
"""Independent finite inductive-invariant and entire-tape block simulation check.
Only Python standard library; no search, optimizer or runtime imports.
"""
import argparse,json,hashlib
from pathlib import Path

def require(ok,msg):
 if not ok:raise ValueError(msg)
def table(p):
 rows={};start=None
 for ln in Path(p).read_text().splitlines():
  if ln.startswith('#! start '):start=int(ln.split()[-1])
  elif ln and not ln.startswith('#'):
   q,b,w,d,z=ln.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return rows,start

def check(old,new,inv):
 T,start=table(old);N,ns=table(new);H=254
 F={int(q):{int(k):v for k,v in facts.items()} for q,facts in inv.items()}
 Q={q for q,b in T};QN={q for q,b in N}
 require(len(Q)==222 and len(QN)==221,'state counts')
 require(start==ns==0 and F[0]=={},'unconstrained start')
 require(set(F)-{H}==Q,'all old states covered')
 require(all((q,b)in T for q in Q for b in(0,1)),'total old table')
 require(all((q,b)in N for q in QN for b in(0,1)),'total new table')
 def phi(q):return 172 if q==192 else q
 require(QN=={phi(q)for q in Q},'quotient states')
 inductive=0;hist={};vacuous=0
 for(q,b),(w,d,z)in T.items():
  if 0 in F[q] and F[q][0]!=b:vacuous+=1;continue
  initial=dict(F[q]);initial[0]=b
  after=dict(initial);after[0]=w
  shifted={k-d:x for k,x in after.items()}
  if z!=H:
   require(z in F,'old successor defined')
   require(all(shifted.get(k)==x for k,x in F[z].items()),f'invariant edge {q}/{b}->{z}')
  inductive+=1
  tape=dict(initial);h=0;s=phi(q);want=phi(z)
  for steps in range(1,66):
   require(h in tape,f'unknown read in block {q}/{b}')
   require((s,tape[h])in N,f'missing new row {s}/{tape[h]}')
   nw,nd,s=N[s,tape[h]];tape[h]=nw;h+=nd
   if z==H:
    if s==H:break
   else:
    require(s!=H,f'interior halt {q}/{b}')
    if s==want and h==d and tape==after:break
  else:raise ValueError(f'no positive exact block {q}/{b}')
  hist[steps]=hist.get(steps,0)+1
 require(F[172].get(-1)==0 and F[192].get(-1)==1,'tag separation')
 return {'status':'PASS_INDUCTIVE_ALL_TAPE_POSITIVE_BLOCK_SIMULATION','old_states':len(Q),'new_states':len(QN),'inductive_rows':inductive,'vacuous_rows':vacuous,'block_length_histogram':hist,'maximum_block':max(hist),'scope':'All initial binary tapes at state0 and all integer head positions. Every old transition is simulated by a positive new block, without an interior halt, preserving the entire tape and head at nonhalting endpoints.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,default=Path(__file__).with_name('prefold.tm'));ap.add_argument('--new',type=Path,default=Path(__file__).with_name('candidate.tm'));ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name('local_proof.json'));ap.add_argument('--output',type=Path);a=ap.parse_args()
 out=check(a.old,a.new,json.loads(a.certificate.read_text())['invariant'])
 out['old_sha256']=hashlib.sha256(a.old.read_bytes()).hexdigest();out['new_sha256']=hashlib.sha256(a.new.read_bytes()).hexdigest()
 text=json.dumps(out,indent=2)+'\n'
 if a.output:a.output.write_text(text)
 print(text,end='')
if __name__=='__main__':main()
