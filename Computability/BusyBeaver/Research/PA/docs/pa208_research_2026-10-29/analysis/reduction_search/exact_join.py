from pathlib import Path
import sys,json,time
from discover_folds import read_table

def exact(t,q,r,context,limit=31,maxnodes=200000):
    # Search bounded common endpoints of both literal trajectories, splitting initial bits.
    init=dict(context)
    # state is (state, head, writes, trace)
    stack=[((q,0,{},[]),(r,0,{},[]),init,[],[],0)]
    cert=[];nodes=0
    while stack:
        old,new,vals,olds,news,phase=stack.pop();nodes+=1
        if nodes>maxnodes:return None,{'reason':'node_budget','nodes':nodes,'cert':len(cert)}
        for oi,oc in enumerate(olds):
            oq,oh,ow,ot=oc
            for ni,nc in enumerate(news):
                nq,nh,nw,nt=nc
                if (r if oq==q else oq,oh)!=(nq,nh):continue
                if all(ow.get(p,vals.get(p,('v',p)))==nw.get(p,vals.get(p,('v',p)))for p in set(ow)|set(nw)):
                    cert.append({'input':vals,'old_trace':ot,'new_trace':nt});break
            else:continue
            break
        else:
            chosen=old if phase==0 else new
            s,h,writes,trace=chosen
            if s==254 or len(trace)>=limit:
                other=new if phase==0 else old
                if other[0]==254 or len(other[3])>=limit:
                    return None,{'reason':'no_join','initial':vals,'old':old,'new':new,'nodes':nodes}
                stack.append((old,new,vals,olds,news,1-phase));continue
            b=writes.get(h,vals.get(h))
            if b is None:
                for v in(0,1):
                    nv=dict(vals);nv[h]=v;stack.append((old,new,nv,olds,news,phase))
                continue
            w,d,z=t[s,b]
            if phase==1 and z==q:z=r
            ws=dict(writes);ws[h]=w
            now=(z,h+d,ws,trace+[[s,h,b,w,d,z]])
            if phase==0:stack.append((now,new,vals,olds+[now],news,1))
            else:stack.append((old,now,vals,olds,news+[now],0))
    return cert,{'nodes':nodes,'cases':len(cert)}

if __name__=='__main__':
    t=read_table(Path(sys.argv[1]));contexts=json.loads(Path(sys.argv[2]).read_text());q=int(sys.argv[3]);r=int(sys.argv[4]);out=Path(sys.argv[5]);limit=int(sys.argv[6])if len(sys.argv)>6 else 31
    cases=[];start=time.monotonic()
    for context in contexts[str(q)]:
        cert,status=exact(t,q,r,context,limit)
        print(q,r,status if cert is not None else {k:v for k,v in status.items() if k not in('old','new')},flush=True)
        if cert is None:out.write_text(json.dumps({'accepted':False,'context':context,'status':status},indent=2)+'\n');break
        cases.append({'context':context,'certificates':cert,'status':status})
    else:out.write_text(json.dumps({'accepted':True,'q':q,'r':r,'cases':cases,'seconds':time.monotonic()-start},indent=2)+'\n')
