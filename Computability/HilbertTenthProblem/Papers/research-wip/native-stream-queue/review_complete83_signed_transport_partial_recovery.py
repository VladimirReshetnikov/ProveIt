#!/usr/bin/env python3
"""Independent partial-transport evidence; no predecessor import/execution."""
from pathlib import Path
import argparse,hashlib,itertools,json
BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs')
AUTHOR=Path('/tmp/complete83_signed_transport_partial_recovery')
PINS={'.md':'5904b0d16501921473de2ef2bfc52dff612450808a4df8c8469f85f6cae848c7','.py':'63eb5647fe1208a78ce5592a48851d4c8d3a9fda2a4efc627d88ae7c1c93b247','.json':'9370a15872113fee2859ab2d1d0e5dd1ad17edfb844cb29d118e00a0cc3499d6'}
def ck(b,m):
 if not b:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def digits(x,V,n):return [(x//V**i)%V for i in range(n)]
def cyclic():
 n=0;negative=0;stoppers=0;h=hashlib.sha256()
 for V,L in [(8,2),(8,3),(16,2),(32,2)]:
  Q=V**L-1
  for pd in itertools.product(range(V-1),repeat=L):
   P=sum(a*V**j for j,a in enumerate(pd))
   if not P:continue
   for nd in itertools.product(range(4),repeat=L):
    N=sum(a*V**j for j,a in enumerate(nd))
    if not N or P==N:continue
    initial=int(P<N);beta=initial;out=[]
    for a,b in zip(pd,nd):
     value=a-b-beta;nextb=int(value<0);out.append(value+V*nextb)
     ck(-4<=value<=V-2 and 0<=out[-1]<V,'single borrow')
     if not b and a:ck(nextb==0,'positive stopper');stoppers+=1
     beta=nextb
    ck(beta==initial and out==digits((P-N)%Q,V,L),'cyclic signed residue')
    h.update(f'{V},{L},{P},{N},{initial}\n'.encode());n+=1;negative+=initial
 return {'cases':n,'negative_difference_cases':negative,'positive_stopper_occurrences':stoppers,'records_sha256':h.hexdigest()}
def geometry():
 cases=stops=targets=0
 for a in range(3,8):
  for k in range(2,7):
   for dummies in (1,3):
    T0=k+3*a
    payload={(r,c,s):T0+(2-r)*3*a+(2-c)*a+s for r in range(3)for c in range(3)for s in range(a)}
    dummy=set(range(T0+9*a,T0+9*a+dummies));low=set(range(k))|set(payload.values())|dummy
    M=max(low)+3*a+1;anchors=[M,3*M,9*M,27*M];E=low|set(anchors);Emax=max(E)
    H=Emax+24*M+3*a+1;T1=H+2*Emax+a+1;T2=T1+2*Emax+1;g=T2+Emax+1;L=2*(g+Emax+1)
    shifts=[3*a,H+a,8*M,24*M];clause=E-dummy
    for T in (T1,T2):
     for f in E-{Emax}:
      ck(Emax+1<T-Emax+f<T,'positive pre-center stopper position');stops+=1
     for shift in shifts+[H,g]:ck(all(shift+f!=T for f in E),'no lower/optional center collision')
     ck(all(Tother-e+f!=T for Tother in (T1,T2)if Tother!=T for e in clause for f in E),'no other-band center collision')
    for target,expected in [(9*M,M),(27*M,3*M)]:
     pairs=[(s,f)for s in shifts for f in E if s+f==target]
     ck(pairs==[(target-expected,expected)],'exact anchor input')
    neg={e+1 for e in E}
    ck(not any(8*M<=e<=9*M or 24*M<=e<=27*M for e in neg),'anchor clean intervals')
    ck([(e,f)for e in E for f in E if f-e==18*M]==[(9*M,27*M)],'unique anchor difference')
    ck(L>2*Emax and Emax+1<33*M<H,'horizontal stopper')
    for r in range(3):
     for c in range(2):
      for s in range(a):
       target=H+payload[r,c,s]
       ck(target>Emax and min(H+j for j in range(k))<target and max(H+j for j in range(k))<target,'right selector stopper')
       got=[(shift,f)for shift in shifts for f in E if shift+f==target]
       ck(got==[(H+a,payload[r,c+1,s])],'horizontal center contribution')
       ck(target-H==payload[r,c,s],'horizontal right contribution');targets+=1
    ck(T2-T1>2*Emax and L-(T2-T1)>Emax,'two-center separation')
    cases+=1
 return {'abstract_layouts':cases,'clean_center_stopper_positions':stops,'horizontal_targets':targets,'actual_compiler_instances':False}
def local():
 obstruction=0;horiz=0
 for A in [4,8,16,32]:
  for V in [2*A,4*A,8*A]:
   for M in range(0,V-1,A):ck(((M-1)%V)&(A-2),'borrowed zero-occupancy clause');obstruction+=1
 for a in range(3,20):
  for s in range(a):
   one=[int(j==s)for j in range(a)];ck(any(x%2 for x in one),'empty/occupied mismatch');horiz+=2
 # Complete finite digit table; the altered vertical example remains allowed locally.
 passing=[]
 for incoming,P,N in itertools.product(range(2),range(3),range(2)):
  raw=P-N-incoming;outgoing=int(raw<0);digit=raw+32*outgoing
  if digit%2==0:passing.append([incoming,P,N,outgoing,digit])
 ck([1,0,1,1,30]in passing,'altered vertical example')
 return {'borrowed_clause_cases':obstruction,'horizontal_mismatch_cases':horiz,'passing_vertical_local_table':passing,'vertical_theorem_claimed_here':False}
def build():
 for e,p in PINS.items():ck(sha(Path(str(AUTHOR)+e).read_bytes())==p,'author pin')
 j=json.loads(Path(str(AUTHOR)+'.json').read_text());pins=[]
 for r in j['dependencies']:
  p=BASE/r['logical_path'];p=p if p.exists()else Path('/tmp')/p.name
  b=p.read_bytes();ck(sha(b)==r['sha256']and len(b)==r['bytes'],'dependency');pins.append(r)
 ck(j['proof_sha256']==PINS['.md']and j['source_sha256']==PINS['.py'],'author receipt bindings')
 return {'author_pins':PINS,'dependency_pins':pins,'helper_sha256':sha(Path(__file__).read_bytes()),'cyclic_subtraction':cyclic(),'geometry':geometry(),'local_lemmas':local(),'scope':{'partial_only':True,'all_size_proof':'independent review Markdown; bounded tests corroborate','predecessor_execution':False,'whole_native_zero':False,'universal83':False}}
def main():
 p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();s=json.dumps(build(),sort_keys=True,indent=2)+'\n'
 if a.output:
  with a.output.open('x')as f:f.write(s)
 else:ck(a.expect.read_text()==s,'receipt mismatch')
 print('PASS independent partial signed-transport review')
if __name__=='__main__':main()
