from pathlib import Path
import json,sys,time,collections
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix,coo_matrix
from scipy.optimize._highspy import _core
import grammar as g

def solve(seq,limit=60,lower=0,outfile='milp_best.json',warm_tree=None):
    root=tuple(seq);freq=collections.Counter(root[i:j] for i in range(len(root)) for j in range(i+2,len(root)+1))
    words=sorted([w for w,n in freq.items() if n>=2],key=lambda w:(len(w),w))+[root]
    index={w:i for i,w in enumerate(words)};N=len(words)
    # Variables first N rule activations, then edge choices.
    edges=[]
    for p,w in enumerate(words):
        for i in range(len(w)):
            edges.append((p,i,i+1,None))
            for j in range(i+2,min(len(w),i+max(map(len,words[:-1])))+1):
                if (i,j)==(0,len(w)):continue
                child=index.get(w[i:j])
                if child is not None:edges.append((p,i,j,child))
    V=N+len(edges)
    c=np.ones(V);c[:N]=-1
    if ('inc1','inc1') in index:c[index[('inc1','inc1')]]-=1
    rows=[];cols=[];vals=[];lb=[];ub=[]
    row=0
    # flow constraint in each phrase.
    flowidx={}
    for p,w in enumerate(words):
        for i in range(len(w)+1):
            flowidx[p,i]=row
            if i==0:rows.append(row);cols.append(p);vals.append(-1)
            elif i==len(w):rows.append(row);cols.append(p);vals.append(1)
            lb.append(0);ub.append(0);row+=1
    for e,(p,i,j,child) in enumerate(edges):
        v=N+e
        rows.extend([flowidx[p,i],flowidx[p,j]]);cols.extend([v,v]);vals.extend([1,-1])
        if child is not None:
            rows.extend([row,row]);cols.extend([v,child]);vals.extend([1,-1]);lb.append(-np.inf);ub.append(0);row+=1
    # root activation
    rows.append(row);cols.append(N-1);vals.append(1);lb.append(1);ub.append(1);row+=1
    if lower:
        for i in range(V):rows.append(row);cols.append(i);vals.append(c[i])
        lb.append(lower);ub.append(np.inf);row+=1
    A=coo_matrix((vals,(rows,cols)),shape=(row,V)).tocsc()
    print('MILP',N,'phrases',len(edges),'edges',row,'constraints',flush=True)
    h=_core._Highs()
    lp=_core.HighsLp()
    lp.num_col_=V;lp.num_row_=row;lp.col_cost_=c;lp.col_lower_=np.zeros(V);lp.col_upper_=np.ones(V);lp.row_lower_=lb;lp.row_upper_=ub
    lp.a_matrix_.format_=_core.MatrixFormat.kColwise;lp.a_matrix_.start_=A.indptr;lp.a_matrix_.index_=A.indices;lp.a_matrix_.value_=A.data
    lp.integrality_=[_core.HighsVarType.kInteger]*V
    h.passModel(lp);h.setOptionValue('time_limit',float(limit));h.setOptionValue('mip_rel_gap',0.0);h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    if warm_tree is not None:
        def small(t):
            if t in g.atoms:return g.atoms[t]
            return small(t[0]),small(t[1])
        tree=small(warm_tree)
        def word(t):return (t,) if isinstance(t,str) else word(t[0])+word(t[1])
        edx={e:N+i for i,e in enumerate(edges)}
        warm=np.zeros(V)
        seen=set()
        def rule(t):
            w=word(t);p=index[w]
            if p in seen:return
            seen.add(p);warm[p]=1
            def parts(t,top=False):
                w=word(t)
                if not top and w in index:
                    rule(t);return [(len(w),index[w])]
                if isinstance(t,str):return [(1,None)]
                return parts(t[0])+parts(t[1])
            i=0
            for ln,ch in parts(t,True):
                warm[edx[p,i,i+ln,ch]]=1;i+=ln
        rule(tree)
        assert np.all(A@warm>=np.array(lb)-1e-6) and np.all(A@warm<=np.array(ub)+1e-6)
        print('WARM',c@warm,flush=True)
        sol=_core.HighsSolution();sol.col_value=warm;h.setSolution(sol)
    h.run()
    from types import SimpleNamespace
    info=h.getInfo();res=SimpleNamespace(x=np.array(h.getSolution().col_value),fun=info.objective_function_value)
    print('RESULT',res.fun,'gap',info.mip_gap,flush=True)
    if not len(res.x):return None
    segs={}
    for e,(p,i,j,ch) in enumerate(edges):
        if res.x[N+e]>.5:segs.setdefault(p,{})[i]=(j,ch)
    cache={}
    def construct(p):
        if p in cache:return cache[p]
        w=words[p];s=[];i=0
        while i<len(w):
            j,ch=segs[p][i];s.append(construct(ch) if ch is not None else g.nodes.get(w[i],w[i]));i=j
        # minimise re-use total via choosing simple leftfold for now
        def fold(v):
            if len(v)==1:return v[0]
            return fold(v[:len(v)//2]),fold(v[len(v)//2:])
        cache[p]=fold(s);return cache[p]
    t=construct(N-1)
    print('EXACT_DAG',g.cost(t),flush=True)
    (Path(__file__).resolve().parents[1]/'results'/outfile).write_text(json.dumps(t))
    return t,res.fun

