"""Untrusted named-syntax certificate producer for the complete R kernel.

No measured checker imports this file. Bound names in fixtures are globally
fresh; substitution below is capture-free under that invariant. The compiler
uses the focused Eq/D object calculus. Q formulas are local clauses only.
"""
import json
from pathlib import Path

Z = ('z',)
_serial = 0

def fresh(prefix='v'):
    global _serial
    _serial += 1
    return prefix + str(_serial)

def V(x): return ('v', x)
def S(t): return ('s', t)
def R(n,a,u,v,h): return ('r',n,a,u,v,h)
def E(s,t): return ('e',s,t)
def Q(y,b): return ('q',y,b)
def D(x,y,b): return ('d',x,y,b)

def sub(a,x,t):
    tag=a[0]
    if tag in ('z','zl'): return a
    if tag=='v': return t if a[1]==x else a
    if tag=='s': return S(sub(a[1],x,t))
    if tag=='r':
        _,n,b,u,v,h=a
        return R(sub(n,x,t),sub(b,x,t),u,v,h if x in (u,v) else sub(h,x,t))
    if tag=='e': return E(sub(a[1],x,t),sub(a[2],x,t))
    if tag=='q': return a if x==a[1] else Q(a[1],sub(a[2],x,t))
    if tag=='d': return a if x in a[1:3] else D(a[1],a[2],sub(a[3],x,t))
    raise ValueError(tag)

def inst(b,x,t,y=None,u=None):
    b=sub(b,x,t)
    return sub(b,y,u) if y is not None else b

def P(kind,goal,**kwargs): return dict(kind=kind,goal=goal,**kwargs)
def comp(a): return P('comp',a)
def hyp(a): return P('hyp',a)
def ref(a): return P('ref',a)

def zero_ax(a=Z):
    u,v=fresh(),fresh()
    return comp(E(R(Z,a,u,v,Z),S(a)))

def succ_ax(n=Z,a=Z,h=None,u=None,v=None):
    u,v=u or fresh(),v or fresh()
    h=h if h is not None else V(v)
    r=R(n,a,u,v,h)
    return comp(E(R(S(n),a,u,v,h),inst(h,u,n,v,r)))

def tr(major,minor,x,body):
    assert major['goal'][0]=='e'
    s,t=major['goal'][1:]
    assert minor['goal']==sub(body,x,s)
    return P('tr',sub(body,x,t),major=major,minor=minor,x=x,body=body)

def refl(t):
    ax=succ_ax(h=t)
    x=fresh()
    return tr(ax,ax,x,E(V(x),t))

def qe(clause,w,minor):
    _,y,b=clause
    assert minor['goal']==sub(b,y,Z)
    return P('qe',sub(b,y,w),major=ref(clause),w=w,minor=minor)

def di(goal,w,mode,z,minor):
    _,x,y,b=goal
    assert minor['goal']==inst(b,x,w,y,S(V(z)))
    assert mode in (0,1) and (not mode or b[0]=='e')
    return P('di',goal,w=w,mode=mode,z=z,minor=minor)

def de(major,a,minor):
    assert major['goal'][0]=='d'
    return P('de',minor['goal'],major=major,a=a,minor=minor)

def identity(goal):
    if goal[0]=='e':
        s,t=goal[1:]
        x=fresh()
        return tr(ref(goal),refl(s),x,E(s,V(x)))
    if goal[0]=='d':
        _,x,y,b=goal
        a,z=fresh(),fresh()
        clause=Q(y,sub(b,x,V(a)))
        base=inst(b,x,V(a),y,Z)
        minor=qe(clause,S(V(z)),hyp(base))
        return de(ref(goal),a,di(goal,V(a),0,z,minor))
    raise ValueError('Only Eq/D object formulas have identity expansion')

class Emitter:
    def __init__(self, focused=True):
        self.focused=focused
        self.k=0
        self.names={}
        self.instructions=[]
        self.counts={}
        self.admin=0
    def n(self,a,env=(),hole=None):
        tag=a[0]
        if tag=='z': return 0
        if tag=='v':
            x=a[1]
            if x in env:return 2*env.index(x)+1
            if x==hole:return 2*len(env)+1
            return self.names[x]
        if tag=='s':return [self.n(a[1],(None,)+env,hole)]
        if tag=='r':
            _,n,b,u,v,h=a
            return [self.n(n,(None,None)+env,hole),self.n(b,(None,None)+env,hole),self.n(h,(v,u)+env,hole)]
        raise ValueError(tag)
    def f(self,a,env=(),hole=None):
        if a[0]=='e':return [self.n(a[1],env,hole),self.n(a[2],env,hole)]
        if a[0]=='q':return [self.f(a[2],(a[1],)+env,hole)]
        if a[0]=='d':return [0,0,self.f(a[3],(a[2],a[1])+env,hole)]
        raise ValueError(a[0])
    def member(self,a,g):return self.f(a) in [self.f(b) for b in g]
    def allocate(self,x=None):
        self.k-=1
        if x is not None:self.names[x]=self.k
        else:self.admin+=1
    def major(self,p,g):
        if self.focused and self.member(p['goal'],g):return
        if p['kind']=='ref' and not self.member(p['goal'],g):raise ValueError('Unavailable major')
        self.go(p,g)
    def go(self,p,g=()):
        goal,kind=p['goal'],p['kind']
        if not self.focused and self.member(goal,g):return
        if kind in ('hyp','ref'):
            if not self.member(goal,g):raise ValueError('Unavailable hypothesis')
            return self.go(identity(goal),g)
        self.counts[kind]=self.counts.get(kind,0)+1
        if kind=='comp':self.instructions.append([0,0,0,0]);return
        if kind=='tr':
            m=p['major']['goal'];s,u=m[1:]
            self.instructions.append([self.f(m),self.n(s),self.n(u),self.f(p['body'],hole=p['x'])])
            self.major(p['major'],g)
            self.allocate()
            self.go(p['minor'],g);return
        if kind=='qe':
            m=p['major']['goal'];_,y,b=m
            self.instructions.append([self.f(m),0,self.n(p['w']),self.f(b,(y,))])
            self.major(p['major'],g)
            self.allocate()
            self.go(p['minor'],g);return
        if kind=='de':
            m=p['major']['goal'];_,x,y,b=m
            self.instructions.append([self.f(m),0,0,0])
            self.major(p['major'],g)
            self.allocate(p['a'])
            self.go(p['minor'],g+(Q(y,sub(b,x,V(p['a']))),));return
        if kind=='di':
            w=self.n(p['w'])
            if not w:raise ValueError('Canonical DI uses nonempty witness encoding')
            self.instructions.append([0 if p['mode'] else [],0,0,w])
            self.allocate(p['z'])
            _,x,y,b=goal
            at=V(p['z']) if p['mode'] else Z
            self.go(p['minor'],g+(inst(b,x,p['w'],y,at),));return
        raise ValueError(kind)
    def run(self,p):
        goal=self.f(p['goal'])
        self.go(p)
        return list(reversed(self.instructions))+[goal]

def fixtures():
    out={}
    out['R_zero']=zero_ax()
    u,v=fresh(),fresh()
    out['R_successor_counter']=succ_ax(S(Z),S(Z),V(u),u,v)
    u,v=fresh(),fresh()
    out['R_successor_state']=succ_ax(S(Z),S(Z),V(v),u,v)
    out['reflexivity_zero']=refl(Z)
    out['reflexivity_nested']=refl(R(S(Z),S(Z),fresh(),fresh(),Z))
    # A nontrivial progress step: R(n,0;u,v.S(v))=S(n).
    x,y,z,u,v=fresh(),fresh(),fresh(),fresh(),fresh()
    r=lambda t:R(t,Z,u,v,S(V(v)))
    body=E(r(V(y)),S(V(y)))
    goal=D(x,y,body)
    ih=E(r(V(z)),S(V(z)))
    ax=succ_ax(V(z),Z,S(V(v)),u,v)
    w=fresh()
    step=tr(ref(ih),ax,w,E(r(S(V(z))),S(V(w))))
    out['DI_progress_uses_hypothesis']=di(goal,S(Z),1,z,step)
    # Constant case matrix uses the local assumption through identity expansion.
    x,y,z=fresh(),fresh(),fresh()
    body=E(Z,Z);goal=D(x,y,body)
    out['DI_case_equation_identity']=di(goal,S(Z),0,z,hyp(body))
    # A D-valued matrix exercises structural expansion of a D hypothesis.
    x,y,z,a,b,c=fresh(),fresh(),fresh(),fresh(),fresh(),fresh()
    inner=D(a,b,E(Z,Z));outer=D(x,y,inner)
    out['DI_case_D_identity']=di(outer,S(Z),0,z,hyp(inner))
    # Eliminate a proved D theorem and specialize its internal Q clause.
    x,y,z,a=fresh(),fresh(),fresh(),fresh()
    body=E(Z,Z);goal=D(x,y,body)
    theorem=di(goal,S(Z),0,z,refl(Z))
    clause=Q(y,body)
    out['DE_QE']=de(theorem,a,qe(clause,S(S(Z)),refl(Z)))
    # Actual existential witness use, with explicit equality transported.
    x,y,z,a,u,v=fresh(),fresh(),fresh(),fresh(),fresh(),fresh()
    r=lambda w:R(S(Z),Z,u,v,w)
    body=E(r(V(x)),V(x));goal=D(x,y,body)
    theorem=di(goal,S(Z),0,z,succ_ax(h=S(Z),u=u,v=v))
    clause=Q(y,E(r(V(a)),V(a)))
    local=qe(clause,S(Z),succ_ax(h=V(a),u=u,v=v))
    hole=fresh()
    # Transport r(a)=a into the constant formula 0=0; a cannot escape.
    out['DE_witness_transport']=de(theorem,a,tr(local,refl(Z),hole,E(Z,Z)))
    return out

def write(directory):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    report=[]
    for focused in (True,False):
        cases=[]
        for name,p in fixtures().items():
            em=Emitter(focused)
            packet=em.run(p)
            cases.append(dict(name=name,accept=True,packet=packet,counts=em.counts,allocations=-em.k,administrative=em.admin))
        filename='focused.json' if focused else 'unfocused.json'
        (directory/filename).write_text(json.dumps(dict(cases=cases),indent=2)+'\n')
        report.append(dict(file=filename,cases=len(cases)))
    return report

if __name__=='__main__':
    import sys
    print(json.dumps(write(sys.argv[1] if len(sys.argv)>1 else Path(__file__).parent/'fixtures'),indent=2))
