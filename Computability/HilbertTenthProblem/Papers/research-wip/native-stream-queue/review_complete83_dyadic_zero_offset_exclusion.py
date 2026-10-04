#!/usr/bin/env python3
"""Independent fresh digit/geometry checks; every predecessor remains inert."""
import argparse,hashlib,itertools,json
from pathlib import Path
BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs')
AUTHOR=Path('/tmp/complete83_dyadic_zero_offset_exclusion')
PINS={'.md':'afa5bf412a150d61deb91e0c5b1eaa17f7f9423c254a93fd1d699221a285adc1','.py':'5ce180ec1e273190fe621cd7d7dc9809d1da92608b531e31f1c46f11a4b35280','.json':'7f187dcbbc5b21d50ea3699a493a5564f5427c59fc8929b20331f884552d088a'}
def ck(b,m):
 if not b:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def blocks():
 count=accepted=0;h=hashlib.sha256();table=[]
 for incoming,P,N in itertools.product(range(2),range(3),range(2)):
  raw=P-N-incoming;out=int(raw<0)
  if raw%2==0:
   ck(not out or (incoming,P,N)==(1,0,1),'unique persistence');table.append([incoming,P,N,out])
 for V in (6,8,32):
  for a in range(3,11):
   for ones in range(3):
    for places in itertools.combinations(range(a),ones):
     N=[int(i in places)for i in range(a)]
     for left,right in itertools.combinations_with_replacement(range(a),2):
      P=[int(i==left)+int(i==right)for i in range(a)]
      for incoming in (0,1):
       beta=incoming;good=True
       for p,n in zip(P,N):
        raw=p-n-beta;nextb=int(raw<0);f=raw+V*nextb
        ck(0<=f<V,'digit range')
        if f%2:good=False;break
        ck(beta or not nextb,'no created borrow');beta=nextb
       count+=1
       if good:
        ck(beta==0,'reset by end')
        if incoming==0:ck(ones%2==0,'negative parity')
        accepted+=1;h.update(f'{V},{a},{places},{left},{right},{incoming}\n'.encode())
 # Exact shift endpoint formula, and the binary terminal-status obstruction.
 endpoints=0
 for a in range(3,33):
  for prev,own in itertools.product(range(a),repeat=2):
   N=[int(prev==a-1)]+[int(own==i-1)for i in range(1,a)]
   ck(sum(N)==1-int(own==a-1)+int(prev==a-1),'shift formula')
   ck((sum(N)%2==0)==((prev==a-1)!=(own==a-1)),'alternation iff even');endpoints+=1
 patterns=0
 for initial,mid2,mid1,mid0,top in itertools.product(range(2),repeat=5):
  statuses=[mid2,mid1,mid0,top,top,top]
  later=[1-statuses[j]+statuses[j-1]for j in range(1,6)]
  ck(later[-2:]==[1,1] and any(n%2 for n in later),'H triple impossible');patterns+=1
 return {'passing_local_table':table,'relaxed_block_assignments':count,'passing_relaxed_blocks':accepted,'passing_records_sha256':h.hexdigest(),'shift_endpoint_pairs':endpoints,'terminal_status_patterns':patterns,'alphabets':[3,10],'even_radices':[6,8,32]}
def geometry():
 count=targets=0;order=[(1,2),(1,1),(1,0),(0,2),(0,1),(0,0)]
 for a in range(3,13):
  for k in range(2,7):
   T0=k+3*a;payload={(r,c,s):T0+(2-r)*3*a+(2-c)*a+s for r in range(3)for c in range(3)for s in range(a)}
   dummy={T0+9*a,T0+9*a+1};low=set(range(k))|set(payload.values())|dummy
   M=max(low)+3*a+1;E=low|{M,3*M,9*M,27*M};emax=max(E)
   H=emax+24*M+3*a+1;T1=H+2*emax+a+1;T2=T1+2*emax+1;g=T2+emax+1
   dc=[3*a,H+a,8*M,24*M,g]+[T-e for T in(T1,T2)for e in E-dummy]
   seq=[payload[r,c,s]for r,c in order for s in range(a)]
   ck(seq==list(range(T0+3*a,T0+9*a)),'six contiguous blocks')
   ck(all(e-1 in payload.values()for e in seq),'all negative predecessors are tile copies')
   for r,c in order:
    for s in range(a):
     e=payload[r,c,s];matches=[(shift,f)for shift in dc+[H]for f in E if shift+f==e]
     ck(matches==[(3*a,payload[r+1,c,s])],'all other positive terms excluded');targets+=1
   ck(seq[0]-1==payload[2,0,a-1],'first predecessor endpoint')
   ck([rc for rc in order[-3:]]==[(0,2),(0,1),(0,0)],'last three top row')
   count+=1
 return {'abstract_layouts':count,'exact_vertical_targets':targets,'order':order,'actual_compiler_outputs':False}
def build():
 for e,p in PINS.items():ck(sha(Path(str(AUTHOR)+e).read_bytes())==p,'author pin')
 j=json.loads(Path(str(AUTHOR)+'.json').read_text());deps=[]
 for r in j['dependencies']:
  p=BASE/r['logical_path'];p=p if p.exists()else Path('/tmp')/p.name
  b=p.read_bytes();ck(sha(b)==r['sha256']and len(b)==r['bytes'],'dependency pin');deps.append(r)
 ck(j['proof_sha256']==PINS['.md']and j['source_sha256']==PINS['.py'],'receipt binding')
 paths=['Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_81.py','Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py']
 code=[(BASE/p).read_text()for p in paths]
 ck('S = (H, H, H, cell(1,' in code[0]and "cell(1, machine.start, 'Q')"in code[0],'literal Start')
 ck('start+(2-r)*3*a+(2-c)*a+s' in code[1],'literal payload geometry')
 return {'author_pins':PINS,'dependencies':deps,'compiler_code_pins':{p:sha((BASE/p).read_bytes())for p in paths},'helper_sha256':sha(Path(__file__).read_bytes()),'generic_borrow_checks':blocks(),'source_geometry_checks':geometry(),'scope':{'actual_compiler_binding':'proof/source read plus pinned literal clauses; abstract finite geometry corroboration','native_zero_evaluation':False,'predecessor_execution':False,'source_or_gate_change':False,'conditional_dyadic_soundness':True,'unconstrained_universal83':False}}
def main():
 p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();s=json.dumps(build(),sort_keys=True,indent=2)+'\n'
 if a.output:
  with a.output.open('x')as f:f.write(s)
 else:ck(a.expect.read_text()==s,'receipt mismatch')
 print('PASS independent dyadic W-zero exclusion')
if __name__=='__main__':main()
