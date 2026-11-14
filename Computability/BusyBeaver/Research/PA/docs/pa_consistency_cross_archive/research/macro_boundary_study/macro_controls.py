"""Independent finite full-tape replay controls for the macro endpoint search."""
import json,hashlib
from pathlib import Path
HERE=Path(__file__).parent
def table(path):
    t={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    return t
def tests(path):
    lines=path.read_text().splitlines();assert len(lines)==int(lines[0])+1
    ans=[]
    for line in lines[1:]:
        v=list(map(int,line.split()));assert len(v)==16
        def cells(words):return {64*k+i for k,w in enumerate(words) for i in range(64) if w>>i&1}
        ans.append((v[:4],cells(v[4:8]),cells(v[8:12])))
    return ans
def replay(t,x,halt=196,root=75):
    (site,pos,goal_halt,steps),start,goal=x
    q=root;h=32;tape=set(start);budget=max(800,2*steps+64)
    for k in range(budget):
        if k and ((goal_halt and q==halt) or (not goal_halt and q==root and h==32 and tape==goal)):
            return 'endpoint',k
        if q==halt:return 'unexpected_halt',k
        if not 0<=h<256:return 'left_finite_window',k
        w,d,q=t[q,int(h in tape)]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    return 'budget_exhausted',budget
base=table(HERE/'upstream/data/pa196.tm');xs=tests(HERE/'macro_tests.txt')
assert all(replay(base,x)[0]=='endpoint' for x in xs)
# Insert a two-step round trip before each root/read-zero transition.
stutter={k:(w,d,198 if z==196 else z) for k,(w,d,z) in base.items()}
old0=stutter[75,0];stutter[75,0]=(0,1,196)
stutter[196,0]=(0,-1,197);stutter[196,1]=(1,-1,197)
stutter[197,0]=old0;stutter[197,1]=stutter[75,1]
stutter_pass=sum(replay(stutter,x,halt=198)[0]=='endpoint' for x in xs)
assert stutter_pass==len(xs)
# Divert every root/read-zero transition to immediate halt.
bad=base.copy();bad[75,0]=(0,1,196)
bad_halt=next((x[0],replay(bad,x)) for x in xs if replay(bad,x)[0]!='endpoint')
assert bad_halt[1][0]=='unexpected_halt'
# The halt site now enters a self-loop, which the bounded checker must reject.
loop=base.copy();loop[63,1]=(1,1,63);loop[63,0]=(0,1,63)
halt_case=next(x for x in xs if x[0][2])
loop_result=replay(loop,halt_case)
assert loop_result[0] in ('left_finite_window','budget_exhausted')
receipt={'baseline_cases':len(xs),'baseline_all_pass':True,
 'stutter_control_cases':stutter_pass,'stutter_extra_controls':2,
 'wrong_halt_control':bad_halt,'nonhalting_control':loop_result,
 'case_file_sha256':hashlib.sha256((HERE/'macro_tests.txt').read_bytes()).hexdigest(),
 'scope':'Finite full-tape controls only; no unbounded source or PA theorem.'}
(HERE/'macro_controls.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
