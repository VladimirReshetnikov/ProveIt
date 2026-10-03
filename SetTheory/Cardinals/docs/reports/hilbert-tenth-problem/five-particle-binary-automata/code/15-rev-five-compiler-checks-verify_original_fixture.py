"""Check original orbit and free/contact boundary fixture directly from the math."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
orbit=json.loads((ROOT/'sample-orbit.json').read_text())
receipt=json.loads((ROOT/'sample-receipt.json').read_text())
boundaries=json.loads((ROOT/'sample-boundary-demonstration.json').read_text())
m=2;p=1;a=0;J=1;D=2*m+4*p;S=2*D+2;B2=D+1;L=3*B2+1;B3=L+D+1;Z=10*B3+10+2*J
ledger=dict(m=m,p=p,a=a,J=J,D=D,S=S,B2=B2,L=L,B3=B3,Z=Z,
 E=2*p+2*p*(2*D+5)+3*p+a,P=2*p+2*p*(2*D+6)+m,
 factors=8*p*D+29*p+m+a,
 radius=4*p*(6*D+8)+(8*p*D+23*p+m)*(24*D+32)+(2*p+a)*(Z+J+12*D+16),
 observer_length=S+D+1,particles=5,alphabet=[0,1])
assert orbit['ledger']==receipt['ledger']==ledger
path=[(0,S,0,0)]
path.extend((2,x,0,0) for x in range(-S,-Z+S-1,-1))
path.extend((3,x,1,0) for x in range(-Z-1+S,-S+1))
path.append((1,S,1,0))
modes=[['H','START'],['H','HALT'],['O','increment-left'],['I','increment-left']]
def encode(n,s):
 mode,x,l,r=n
 return sorted([-(Z+l),0,Z+r,x,x+2*mode+(1 if s=='+' else 2)])
T=len(path)-1
frames=[(n,'+') for n in path]+[(n,'-') for n in reversed(path)]
assert T==696 and len(frames)==1394
assert len({tuple(encode(n,s)) for n,s in frames})==len(frames)
assert orbit['first_halt']==receipt['first_halt']==T
assert orbit['reflection_period']==receipt['reflection_period']==len(frames)
assert orbit['observer_hits']==[T]
assert receipt['initial_ones']==encode(path[0],'+')
assert receipt['halt_ones']==encode(path[-1],'+')
assert len(orbit['states'])==len(frames)
for t,(row,(n,s)) in enumerate(zip(orbit['states'],frames)):
 assert row==dict(t=t,ones=encode(n,s),mode=modes[n[0]],phase=s,halt_observer=t==T),(t,row)
assert len(boundaries)==receipt['boundary_tests']==4
for row in boundaries:
 t=row['t'];node=path[t];mode,x,l,r=node
 assert mode==2
 if abs(x)<=L:
  gate=f"behind:('O', 'increment-left'):{abs(x)}"
 elif abs(x+Z)<=L:
  gate=f"ahead:('O', 'increment-left'):{abs(x+Z)}"
 else:gate="free:('O', 'increment-left')"
 assert row==dict(t=t,input_ones=encode(node,'+'),input_anchor=x,edge_gate=gate,
                  after_E_ones=encode(path[t+1],'-'),reverse_edge_gate=gate)
assert receipt['status']=='passed'
result=dict(status='passed',method='Independent mathematical micro-path reconstruction, without compiler/API imports',
 frames_checked=len(frames),distinct_frames=len(frames),first_halt=T,reflection_period=len(frames),
 boundary_records_checked=len(boundaries),factors=ledger['factors'],radius=ledger['radius'],
 fixture_files=['sample-orbit.json','sample-receipt.json','sample-boundary-demonstration.json'])
(ROOT/'checks'/'original-fixture-independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
