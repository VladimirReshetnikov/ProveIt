"""Independent scalar stream theorem and real delayed-loader queue checks."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import explore_delayed_blank_raw_queue as queue

cases=0
for m in range(1,4):
    W=3**m
    for t in range(4):
        q=3**t
        for I in range(W):
            for A in range(q):
                N=I;actual_D=0
                for j in range(t):
                    head=N%3;append=A//3**j%3
                    actual_D+=head*3**j
                    N=(N-head)//3+append*(W//3)
                    assert 0<=N<W
                assert actual_D==I+W*A-q*N
                for D in range(q):
                    assert (D==I+W*A)==(D==actual_D and N==0)
                    cases+=1

accepting=0
def check_streams(rows,R,W,x,L):
    global accepting
    D=[0,0];A=[0,0];q=1
    for coord,removed,appended in rows:
        for i in range(2):
            D[i]+=removed[i]*q;A[i]+=appended[i]*q
        q*=3
    assert W==3*L and 0<=x<L
    assert min(D+A)>0 and max(D+A)<q
    assert D==[x+W*A[0],L+W*A[1]]
    assert q> L
    # Replay solely from stream digits and the initial coordinate values.
    content=[x,L]
    for j in range(len(rows)):
        heads=[D[i]//3**j%3 for i in range(2)]
        out=[A[i]//3**j%3 for i in range(2)]
        assert heads==[content[i]%3 for i in range(2)]
        for i in range(2):content[i]=(content[i]-heads[i])//3+(W//3)*out[i]
    assert content==[0,0]
    accepting+=1
    return q

queue.pack_and_check=check_streams
loader=queue.exhaustive_loader()
runs=queue.runs()
assert accepting==loader['positive_transports']+runs['positive_transports']==463
print(dict(status='PASS_BASE_THREE_STREAM_CAUSALITY',exhaustive_scalar_cases=cases,
           real_accepting_controller_words=accepting,stream_operations=4,
           delayed_input_operations=2,total_component_operations=6,
           scope='Controller words, common base3 powers and bounded trit streams assumed; no complete certificate count'))
