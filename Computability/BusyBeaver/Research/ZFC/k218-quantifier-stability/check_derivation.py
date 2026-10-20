#!/usr/bin/env python3
"""Finite schematic Hilbert derivations, with theorem-only GEN and literal gates.

All AST arguments denote native natural-number codes. I/Q/R/E are the exact
Code254 constructors; zero is native truth. Structural equality is sufficient,
not necessary, for equality of instantiated native codes (I(0,0)=0 is allowed).
No constructor injectivity or substitution rule is used by this proof checker.
"""
import hashlib,json
from pathlib import Path
T=('zero',)
def P(x):return ('parameter',x)
def I(a,b):return ('I',a,b)
def Q(i,a):return ('Q',i,a)
def R(a,b):return ('R',a,b)
def E(a,b):return ('E',a,b)
F=R(T,T)
def N(a):return I(a,F)
def NN(a):return N(N(a))
def Ex(i,a):return N(Q(i,N(a)))
def fresh(a,b):return ('max_plus_one',a,b)
def req(b,k,m):return Q(b,I(m,N(Q(b,I(m,N(R(b,k)))))))
def clos(a,b,k,m):return Q(b,I(R(b,k),N(Q(a,I(m,N(Q(a,I(Q(k,I(R(k,a),R(k,b))),req(b,k,m)))))))))
def nks(a,b,c):return Q(c,I(clos(a,b,c,c),N(req(b,c,c))))
def ax_formula(name,a):
    if name=='truth':assert not a;return T
    if name=='K':x,y=a;return I(x,I(y,x))
    if name=='S':x,y,z=a;return I(I(x,I(y,z)),I(I(x,y),I(x,z)))
    if name=='rho1':i,b=a;return Ex(i,E(i,b))
    if name=='rho2':i,x,y=a;return I(Q(i,I(x,y)),I(Q(i,x),Q(i,y)))
    if name=='rho6':i,x=a;return I(Ex(i,Q(i,x)),x)
    if name=='G':a,b,c=a;return I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
    if name=='bundle':
        x,y,c=a;assert c==fresh(x,y) # explicit arithmetic witness c=max(x,y)+1
        return N(I(I(R(x,y),Q(c,R(x,y))),nks(x,y,c)))
    if name=='Q_stability':i,x=a;return I(NN(Q(i,x)),Q(i,x))
    raise ValueError(name)

nodes=[];intern={}
def put(rule,formula,parents=(),args=(),opened=frozenset()):
    key=(rule,formula,parents,args,opened)
    if key in intern:return intern[key]
    k=len(nodes);nodes.append({'rule':rule,'formula':formula,'parents':parents,'args':args,'open':opened});intern[key]=k;return k
def form(p):return nodes[p]['formula']
def ax(name,*args):return put(name,ax_formula(name,args),args=args)
def hyp(a):
    k=len(nodes);return put('hyp',a,args=(k,),opened=frozenset([k]))
def mp(major,minor):
    f=form(major);assert f[0]=='I' and f[1]==form(minor)
    return put('mp',f[2],(major,minor),opened=nodes[major]['open']|nodes[minor]['open'])
def gen(i,p):assert not nodes[p]['open'];return put('gen',Q(i,form(p)),(p,),args=(i,))
def ident(a):return mp(mp(ax('S',a,I(a,a),a),ax('K',a,I(a,a))),ax('K',a,a))
dm={}
def ded(h,p):
    key=h,p
    if key in dm:return dm[key]
    a=form(h);f=form(p);n=nodes[p]
    if p==h:q=ident(a)
    elif h not in n['open']:q=mp(ax('K',f,a),p)
    else:
        assert n['rule']=='mp';major,minor=n['parents'];b=form(minor)
        q=mp(mp(ax('S',a,b,f),ded(h,major)),ded(h,minor))
    assert form(q)==I(a,f) and nodes[q]['open']==n['open']-{h}
    dm[key]=q;return q
def efq(a):
    h=hyp(F);e=Ex(T,Q(T,a));return ded(h,mp(ax('rho6',T,a),mp(ax('K',F,Q(T,N(Q(T,a)))),h)))
def normal(i,p):
    f=form(p);assert f[0]=='I';return mp(ax('rho2',i,f[1],f[2]),gen(i,p))
def serial(i):
    e=E(i,T);h=hyp(Q(i,F));q=mp(normal(i,efq(N(e))),h)
    return ded(h,mp(ax('rho1',i,T),q))
def double(p):
    h=hyp(N(form(p)));return ded(h,mp(h,p))
def existential_mono(i,p):
    _,x,y=form(p);ny=hyp(N(y));hx=hyp(x)
    contra=ded(ny,ded(hx,mp(ny,mp(p,hx))))
    q=normal(i,contra);ex=hyp(Ex(i,x));qy=hyp(Q(i,N(y)))
    return ded(ex,ded(qy,mp(ex,mp(q,qy))))
def persistence_stable(a,i,p):
    assert form(p)==NN(I(a,Q(i,a))) and not nodes[p]['open']
    qa=Q(i,a);z=Q(i,N(qa))
    ha=hyp(a);nqa=hyp(N(qa));pers=hyp(I(a,qa))
    n_pers=ded(pers,mp(nqa,mp(pers,ha)))
    hprime=ded(ha,ded(nqa,mp(p,n_pers))) # a -> NN(Q a)
    hz=hyp(z);hqa=hyp(qa)
    qnnqa=mp(normal(i,hprime),hqa)
    qf=mp(mp(ax('rho2',i,N(qa),F),qnnqa),hz)
    z_nqa=ded(hz,ded(hqa,mp(serial(i),qf)))
    hz2=hyp(z);ha2=hyp(a)
    z_na=ded(hz2,ded(ha2,mp(mp(hprime,ha2),mp(z_nqa,hz2))))
    nna=hyp(NN(a));hz3=hyp(z)
    nz=ded(hz3,mp(nna,mp(z_na,hz3)))
    return ded(nna,mp(ax('rho6',i,a),nz))
def rel_stable(a,b):
    c=fresh(a,b);v=I(R(a,b),Q(c,R(a,b)));j=nks(a,b,c)
    nv=hyp(N(v));hv=hyp(v)
    vi_j=ded(hv,mp(efq(j),mp(nv,hv)))
    nnv=ded(nv,mp(ax('bundle',a,b,c),vi_j))
    return persistence_stable(R(a,b),c,nnv)
def eq_refl(a):
    k=R(a,a);x=E(k,a);e=E(a,a);h=hyp(x)
    p=ded(h,mp(mp(ax('G',a,a,k),h),h))
    ex=mp(existential_mono(k,p),ax('rho1',k,a))
    return mp(ax('rho6',k,e),ex)
def eq_stable(a,b):
    p=mp(ax('G',a,b,a),eq_refl(a))
    return persistence_stable(E(a,b),R(a,b),double(p))
def imp_stable(a,b,pb):
    assert form(pb)==I(NN(b),b)
    ni=hyp(NN(I(a,b)));ha=hyp(a);nb=hyp(N(b));iab=hyp(I(a,b))
    niab=ded(iab,mp(nb,mp(iab,ha)))
    nnb=ded(nb,mp(ni,niab))
    return ded(ni,ded(ha,mp(pb,nnb)))
def top_stable():return mp(ax('K',T,NN(T)),ax('truth'))
def peirce(a,b,sa):
    h=hyp(I(I(a,b),a));na=hyp(N(a));ha=hyp(a)
    ab=ded(ha,mp(efq(b),mp(na,ha)))
    nna=ded(na,mp(na,mp(h,ab)))
    return ded(h,mp(sa,nna))
def full_L(a,b,c,u,sc):
    h=hyp(I(I(c,u),a));k=hyp(I(a,c));hb=hyp(b);nc=hyp(N(c));hc=hyp(c)
    cu=ded(hc,mp(efq(u),mp(nc,hc)))
    nnc=ded(nc,mp(nc,mp(k,mp(h,cu))))
    # hb is deliberately unused: weakening is explicit in ded.
    return ded(h,ded(k,ded(hb,mp(sc,nnc))))
def stable(t):
    if t==T:return top_stable()
    tag=t[0]
    if tag=='R':return rel_stable(t[1],t[2])
    if tag=='E':return eq_stable(t[1],t[2])
    if tag=='Q':return ax('Q_stability',t[1],t[2])
    if tag=='I':return imp_stable(t[1],t[2],stable(t[2]))
    raise ValueError('No stability assumption for arbitrary parameter: '+repr(t))

def validate():
    for k,n in enumerate(nodes):
        rule=n['rule'];ps=n['parents'];assert all(0<=p<k for p in ps)
        if rule=='hyp':assert n['open']==frozenset([k]) and n['args']==(k,)
        elif rule=='mp':
            a,b=ps;assert form(a)==I(form(b),n['formula']);assert n['open']==nodes[a]['open']|nodes[b]['open']
        elif rule=='gen':
            assert not nodes[ps[0]]['open'] and not n['open']
            assert n['formula']==Q(n['args'][0],form(ps[0]))
        else:assert not ps and not n['open'] and n['formula']==ax_formula(rule,n['args'])
    return True
def main():
    a,b,c,u,i=map(P,('A','B','C','U','i'));outputs={}
    outputs['explosion']=efq(a);outputs['seriality']=serial(i)
    outputs['membership_stability']=rel_stable(a,b);outputs['equality_reflexivity']=eq_refl(a);outputs['equality_stability']=eq_stable(a,b)
    outputs['truth_zero_stability']=top_stable();outputs['quantified_stability']=stable(Q(i,a))
    sb=hyp(I(NN(b),b));outputs['implication_stability_from_consequent']=ded(sb,imp_stable(a,b,sb))
    sa=hyp(I(NN(a),a));outputs['peirce_from_stability']=ded(sa,peirce(a,b,sa))
    sc=hyp(I(NN(c),c));outputs['full_rho8_from_stability']=ded(sc,full_L(a,b,c,u,sc))
    samples=[T,R(a,b),E(a,b),I(R(a,b),E(a,b)),Q(i,a),I(Q(i,a),R(b,a)),I(T,T),I(T,Q(i,T))]
    for k,t in enumerate(samples):outputs['sample_stability_'+str(k)]=stable(t)
    assert validate() and all(not nodes[p]['open'] for p in outputs.values())
    def native_eval(t,env):
        if t==T:return 0
        if t[0]=='parameter':return env[t[1]]
        x,y=native_eval(t[1],env),native_eval(t[2],env)
        if t[0]=='max_plus_one':return max(x,y)+1
        pair=(x+y)*(x+y+1)//2+y
        return 4*pair+{'I':0,'R':1,'Q':2,'E':3}[t[0]]
    assert native_eval(I(T,T),{})==native_eval(T,{})==0
    rec={'status':'SCHEMATIC_HILBERT_DERIVATIONS_CHECKED','checker':'own executable proof-DAG reader, not Lean/Rocq','nodes':len(nodes),'outputs':{k:{'node':v,'formula':form(v),'closed':True} for k,v in outputs.items()},
      'axiom_schemas_used':sorted({n['rule'] for n in nodes if n['rule'] not in ('mp','gen','hyp')}),'gen_only_on_closed_theorems':True,'bundle_gates':'c=max(a,b)+1, so c differs from both endpoints for every natural assignment','native_zero_alias_checked':True,'scope':'Finite parametric K/S+retained-row+Q-stability derivations; full arbitrary-native-code DNE follows by the separately stated strong induction. No machine/compiler/state-count claim.'}
    out=Path(__file__).parent
    (out/'result.json').write_text(json.dumps(rec,indent=2)+'\n')
    serialized_nodes=[{**n,'open':sorted(n['open'])} for n in nodes]
    (out/'proof-dag.json').write_text(json.dumps({'nodes':serialized_nodes,'outputs':outputs},separators=(',',':'))+'\n')
    print(json.dumps({'status':rec['status'],'nodes':len(nodes),'outputs':len(outputs),'proof_bytes':(out/'proof-dag.json').stat().st_size}))
if __name__=='__main__':main()
