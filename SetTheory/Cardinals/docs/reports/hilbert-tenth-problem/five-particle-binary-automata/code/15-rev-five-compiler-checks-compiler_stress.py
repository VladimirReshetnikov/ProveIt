"""Finite shape/phase stress test of COMPILER_PROOF.md on a partial-injective source.
This tests actual gate isolation/guards on encoded configurations, not full-shift
reversibility (which follows from the separate lemma).
"""
from collections import defaultdict
MCONTROLS=5  # q4 is a halt control with no outgoing branch.
# e0,e1 merge at q1 with disjoint exact images; e2/e3 decrement opposite sides.
branches=[(0,1,-1,1,lambda l,r:l==0),
          (0,1,1,1,lambda l,r:l>1 and r==0),
          (1,2,-1,-1,lambda l,r:l>0),
          (2,3,1,-1,lambda l,r:r>0),
          (3,0,0,0,lambda l,r:True)]
p=4;a=1;J=2
D=2*MCONTROLS+4*p;S=2*D+2;B2=D+1;L=3*B2+1;B3=L+D+1;Z=10*B3+10+2*J
modes=[('H',q) for q in range(MCONTROLS)]+[(kind,e) for e in range(p) for kind in ['O','I']]
gap={(u,s):2*i+(1 if s=='+' else 2) for i,u in enumerate(modes) for s in '+-'}
E=[];P=[]

def add(block, name, b, pp, ph, pm, qq, qh, qm, guard=None):
    block.append(dict(name=name,b=b,ends=[(frozenset(pp),ph,gap[pm]),(frozenset(qq),qh,gap[qm])],guard=guard))

def image_guard(e,l,r):
    q,qp,v,d,g=branches[e]
    oldl=l-d if v==-1 else l
    oldr=r-d if v==1 else r
    return oldl>=0 and oldr>=0 and g(oldl,oldr)

for e in range(p):
    q,qp,v,d,g=branches[e]
    for kind,w in [('O',v),('I',-v)]:
        u=(kind,e);dp=gap[u,'+'];dm=gap[u,'-']
        add(E,f'free {u}',B2,[0,dp],0,(u,'+'),[w,w+dm],w,(u,'-'))
        for t in range(S,L+1):
            add(E,f'behind {u} {t}',B3,[0,w*t,w*t+dp],w*t,(u,'+'),[0,w*(t+1),w*(t+1)+dm],w*(t+1),(u,'-'))
        for t in range(S+1,L+1):
            add(E,f'ahead {u} {t}',B3,[0,-w*t,-w*t+dp],-w*t,(u,'+'),[0,-w*(t-1),-w*(t-1)+dm],-w*(t-1),(u,'-'))
        add(P,f'phase free {u}',B2,[0,dp],0,(u,'+'),[0,dm],0,(u,'-'))
        for s in [-1,1]:
            for t in range(S,L+1):
                add(P,f'phase triple {u} {s} {t}',B3,[0,s*t,s*t+dp],s*t,(u,'+'),[0,s*t,s*t+dm],s*t,(u,'-'))
    hp=('H',q);op=('O',e);ip=('I',e);hq=('H',qp)
    add(E,f'dispatch {e}',B3,[0,S,S+gap[hp,'+']],S,(hp,'+'),[0,v*S,v*S+gap[op,'-']],v*S,(op,'-'),g)
    add(E,f'endpoint {e}',B3,[0,-v*S,-v*S+gap[op,'+']],-v*S,(op,'+'),[v*d,v*d-v*S,v*d-v*S+gap[ip,'-']],v*d-v*S,(ip,'-'))
    add(E,f'commit {e}',B3,[0,v*S,v*S+gap[ip,'+']],v*S,(ip,'+'),[0,S,S+gap[hq,'-']],S,(hq,'-'),lambda l,r,e=e:image_guard(e,l,r))
for e in range(p,len(branches)):
    q,qp,v,d,g=branches[e];hp=('H',q);hq=('H',qp)
    add(E,f'zero {e}',B3,[0,S,S+gap[hp,'+']],S,(hp,'+'),[0,S,S+gap[hq,'-']],S,(hq,'-'),g)
for q in range(MCONTROLS):
    u=('H',q)
    add(P,f'phase home {q}',B3,[0,S,S+gap[u,'+']],S,(u,'+'),[0,S,S+gap[u,'-']],S,(u,'-'))
assert len(E)+len(P)==8*p*D+29*p+MCONTROLS+a
for gate in E+P:
    for pp,head,gg in gate['ends']:
        assert min(pp)>=-gate['b'] and max(pp)<=gate['b']
        assert len(pp) in [2,3]
    pp,qq=gate['ends'][0][0],gate['ends'][1][0]
    assert {x-min(pp) for x in pp}!={x-min(qq) for x in qq}

def index(gates):
    idx=defaultdict(list)
    for gate in gates:
        for side,(_,__,gg) in enumerate(gate['ends']):idx[gg].append((gate,side))
    return idx
EI=index(E);PI=index(P)

def conf(u,x,l,r,s):
    return frozenset([-(Z+l),0,Z+r,x,x+gap[u,s]])

def active(idx,u,x,l,r,s):
    ones=conf(u,x,l,r,s);out=[]
    for gate,side in idx[gap[u,s]]:
        pp,ph,gg=gate['ends'][side];key=x-ph;b=gate['b']
        # On admissible geometry every raw match must use the sole close pair,
        # making this the gate's only possible raw key.
        if frozenset(z-key for z in ones if abs(z-key)<=b)!=pp:continue
        if frozenset(z-key for z in ones if abs(z-key)<=3*b+1)!=pp:continue
        if gate['guard'] is not None:
            lc=[k for k in range(J+1) if key-Z-k in ones]
            rc=[k for k in range(J+1) if key+Z+k in ones]
            if len(lc)>1 or len(rc)>1:continue
            if not gate['guard'](lc[0] if lc else J+1,rc[0] if rc else J+1):continue
        qq=gate['ends'][1-side][0]
        out.append((gate['name'],(ones-{key+z for z in pp})|{key+z for z in qq}))
    return out

def phase_check(state,s):
    u,x,l,r=state
    out=active(PI,u,x,l,r,s)
    assert len(out)==1,("phase count",state,s,[a[0] for a in out])
    assert out[0][1]==conf(u,x,l,r,'-' if s=='+' else '+')

edges=0;states=0
for e,(q,qp,v,d,g) in enumerate(branches):
    for l in range(3):
        for r in range(3):
            if not g(l,r):continue
            start=(('H',q),S,l,r)
            if not d:
                path=[start,(('H',qp),S,l,r)]
            else:
                path=[start]
                target=v*(Z+(l if v==-1 else r))
                x=v*S
                while True:
                    path.append((('O',e),x,l,r))
                    if x==target-v*S:break
                    x+=v
                ll=l+d if v==-1 else l;rr=r+d if v==1 else r
                x=target+v*d-v*S
                while True:
                    path.append((('I',e),x,ll,rr))
                    if x==v*S:break
                    x-=v
                path.append((('H',qp),S,ll,rr))
                assert len(path)-1==3+2*(Z+(l if v==-1 else r))+d-4*S
            for aa,bb in zip(path,path[1:]):
                for state,s,expected,es in [(aa,'+',bb,'-'),(bb,'-',aa,'+')]:
                    u,x,cl,cr=state
                    out=active(EI,u,x,cl,cr,s)
                    assert len(out)==1,("edge count",e,state,s,[a[0] for a in out])
                    assert out[0][1]==conf(*expected,es),("edge target",e,state,s,out)
                    phase_check(state,s);states+=1
                edges+=1
# Both signs of every home, including blocked branches and incoming-domain gaps.
for q in range(MCONTROLS):
    for l in range(5):
        for r in range(5):
            for s in '+-':
                wanted=sum(qq==q and g(l,r) for qq,qp,v,d,g in branches) if s=='+' else sum(qp==q and image_guard(e,l,r) for e,(qq,qp,v,d,g) in enumerate(branches))
                out=active(EI,('H',q),S,l,r,s)
                assert len(out)==wanted,("home matching",q,l,r,s,wanted,[a[0] for a in out])
                assert wanted<=1
                phase_check((('H',q),S,l,r),s)
print(f'PASS: {len(E)+len(P)} gates; {edges:,} source-path microedges ({states:,} signed endpoint checks); 250 signed homes. Exact image guards, free/contact boundaries, interaction endpoints, phase uniqueness, support bounds, nontranslation, timing, and factor count verified.')
