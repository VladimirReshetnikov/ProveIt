"""Independently reconstruct every clean-target fixture frame from the math.
No imports from the compiler implementation or API test modules.
"""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
source=json.loads((ROOT/'clean-target-sample-source.json').read_text())
original=json.loads((ROOT/'sample-source.json').read_text())
orbit=json.loads((ROOT/'clean-target-sample-orbit.json').read_text())
receipt=json.loads((ROOT/'clean-target-sample-receipt.json').read_text())
assert original['controls']==['START','HALT'] and original['start']=='START' and original['halt']=='HALT'
assert original['branches']==[{'name':'increment-left','source':'START','target':'HALT','side':-1,'delta':1,'guard':{'op':'true'}}]
assert source['controls']==['F:START','F:HALT','B:START','B:HALT','CLEAN-HALT']
assert source['start']=='F:START' and source['halt']=='CLEAN-HALT' and source['class_cut']==1
assert [(b['source'],b['target'],b['side'],b['delta'],b['guard']) for b in source['branches']]==[
 ('F:START','F:HALT',-1,1,{'op':'true'}),
 ('B:HALT','B:START',-1,-1,{'op':'gt','counter':0,'value':0}),
 ('F:HALT','B:HALT',-1,0,{'op':'true'}),
 ('B:START','CLEAN-HALT',-1,0,{'op':'true'})]
m=5;p=2;a=2;J=1
D=2*m+4*p;S=2*D+2;B2=D+1;L=3*B2+1;B3=L+D+1;Z=10*B3+10+2*J
pairs=4*p;triples=8*p*D+23*p+m;contexts=2*p+a
R=pairs*(6*D+8)+triples*(24*D+32)+contexts*(Z+J+12*D+16)
ledger=dict(m=m,p=p,a=a,J=J,D=D,S=S,B2=B2,L=L,B3=B3,Z=Z,
 E=2*p+2*p*(2*D+5)+3*p+a,P=2*p+2*p*(2*D+6)+m,
 factors=pairs+triples+contexts,radius=R,observer_length=S+D+1,particles=5,alphabet=[0,1])
assert ledger==receipt['ledger']==orbit['ledger']
# An unsigned node is (mode index, head anchor, left counter, right counter).
# Mode indices 0..4 are the listed homes, then O_F,I_F,O_B,I_B.
path=[(0,S,0,0)]
def nonzero_leg(out_mode,in_mode,target_home,left,delta):
    m_old=-(Z+left)
    path.extend((out_mode,x,left,0) for x in range(-S,m_old+S-1,-1))
    new_left=left+delta;m_new=-(Z+new_left)
    path.extend((in_mode,x,new_left,0) for x in range(m_new+S,-S+1))
    path.append((target_home,S,new_left,0))
nonzero_leg(5,6,1,0,1)
theta=len(path)-1
path.append((3,S,1,0)) # F:HALT -> B:HALT
nonzero_leg(7,8,2,1,-1)
path.append((4,S,0,0)) # B:START -> CLEAN-HALT
first=len(path)-1

def encode(node,sign):
    mode,x,l,r=node
    d=2*mode+(1 if sign=='+' else 2)
    return sorted([-(Z+l),0,Z+r,x,x+d])
expected=[encode(n,'+') for n in path]+[encode(n,'-') for n in reversed(path)]
assert len(expected)==len({tuple(c) for c in expected})
assert theta==1416 and first==2*theta+2==2834 and len(expected)==4*theta+6==5670
assert orbit['input_counters']==[0,0]
assert orbit['forward_original_leg']==receipt['theta']==theta
assert orbit['first_exact_target']==receipt['first_exact_target']==first
assert orbit['reflection_period']==receipt['reflection_period']==len(expected)
assert orbit['exact_target_ones']==receipt['target_ones']==expected[first]
assert receipt['initial_ones']==expected[0]
assert receipt['exact_target_hits']==[first]
assert len(orbit['states'])==len(expected)
for t,(row,wanted) in enumerate(zip(orbit['states'],expected)):
    assert row=={'t':t,'ones':wanted,'exact_target':t==first},(t,row,wanted)
assert receipt['status']=='passed'
result=dict(status='passed',method='Independent mathematical micro-path reconstruction, without compiler/API imports',
            frames_checked=len(expected),distinct_frames=len(expected),first_exact_target=first,
            reflection_period=len(expected),theta=theta,factors=ledger['factors'],radius=R,
            source_files=['sample-source.json','clean-target-sample-source.json'],
            fixture_files=['clean-target-sample-orbit.json','clean-target-sample-receipt.json'])
(ROOT/'checks'/'clean-fixture-independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
