from search_merges import load,contexts
from pathlib import Path
import sys,json,time

def route(m,pat,r,q,s,bound=25):
    seen=set();lens=set()
    for orig in pat:
        read=(orig>>r)&1;w,d,target=m[q,read]
        final=(orig&~(1<<r))|(w<<r);end=r+(1 if d=='R' else -1)
        x=r;state=s;t=orig
        for k in range(bound+1):
            if x==end and state==target and t==final:
                lens.add(k);break
            if state==q or x<0 or x>2*r or (state,(t>>x)&1) not in m:return
            seen.add(state)
            v=(t>>x)&1;w,d,state=m[state,v]
            t=(t&~(1<<x))|(w<<x);x+=1 if d=='R' else -1
        else:return
    return seen,lens

if __name__=='__main__':
    t=time.time();r=int(sys.argv[1]) if len(sys.argv)>1 else 4
    m=load(Path(__file__).with_name('pa196.tm'));ctx=contexts(m,r)
    out=[]
    for q in ctx:
        if q==0:continue
        for s in ctx:
            if q==s:continue
            val=route(m,ctx[q],r,q,s)
            if val:
                print(q,'->',s, sorted(val[1]),sorted(val[0]),flush=True)
                out.append((q,s,sorted(val[1]),sorted(val[0])))
    print('Seconds:',time.time()-t)
