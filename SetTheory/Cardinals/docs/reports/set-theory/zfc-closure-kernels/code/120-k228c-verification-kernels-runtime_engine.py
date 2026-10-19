"""Literal unary/list induction engine, specialized to normalized K230 labels.

The computational definitions are retained from the pinned 235 predecessor
engine. Only the four list-entry state labels are specialized to K230.
No supplied tape, proof source, or parameter value is executed as code.
"""
import runtime_support as r

NV=13
ZERO=(0,)*NV

def num(n):return (n,)+(0,)*(NV-1)
def var(i):return tuple(int(j==i) for j in range(NV))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def minus1(a):return (a[0]-1,)+a[1:]
def nonnegative(a):return all(x>=0 for x in a)
def run(bit,n):return ('run',bit,n if isinstance(n,tuple) else num(n))
def bit(b):return run(b,1)
def block(value,family='B'):
    # B(v)=0 1^(v+1), C(v)=1 0 1^v.
    return [bit(0),run(1,add(value,num(1)))] if family=='B' else [bit(1),bit(0),run(1,value)]
def tail(family='B',reverse=False):return ('list',family,'spare_tail',reverse)
BLANK=('blank',)
def rev(atoms):
    return [a if a[0]!='list' else (a[0],a[1],a[2],not a[3]) for a in reversed(atoms)]

def normal(atoms):
    out=[]
    for a in atoms:
        if a[0]=='run':
            assert a[1] in (0,1) and nonnegative(a[2]),('negative run',a)
            if a[2]==ZERO:continue
            if out and out[-1][0]=='run' and out[-1][1]==a[1]:
                a=run(a[1],add(out.pop()[2],a[2]))
        out.append(a)
    # An infinite zero exterior absorbs any finite adjacent zero run.
    if len(out)>1 and out[-1]==BLANK and out[-2][0]=='run' and out[-2][1]==0:out.pop(-2)
    # Finite-list word identity, proved by base/cons algebra independently below:
    # C(A) 1 = 1 B(A), and its reversal 1 rev(C(A)) = rev(B(A)) 1.
    for i in range(len(out)-1):
        a,b=out[i:i+2]
        if a[:2]==('list','C') and not a[3] and b[:2]==('run',1) and b[2][0]>=1:
            return normal(out[:i]+[bit(1),('list','B',a[2],False),run(1,minus1(b[2]))]+out[i+2:])
        if a[:2]==('run',1) and a[2][0]>=1 and b[:2]==('list','C') and b[3]:
            return normal(out[:i]+[run(1,minus1(a[2])),('list','B',b[2],True),bit(1)]+out[i+2:])
    return out

class State:
    def __init__(self,q,left,right,direction=1):self.q=q;self.left=list(left);self.right=list(right);self.direction=direction
    def key(self):
        self.left=normal(self.left);self.right=normal(self.right)
        return self.q,self.direction,self.left,self.right
    def step(self,table,lemmas,clock,motion):
        self.key()
        src,dst=(self.right,self.left) if self.direction==1 else (self.left,self.right)
        if not src:raise AssertionError('Unrepresented tape exterior')
        a=src[0]
        if a==BLANK:src.insert(0,bit(0));a=src[0]
        if a[0]=='list':
            key=(self.q,self.direction,a[1],a[3])
            assert key in lemmas,('No checked list traversal',key)
            src.pop(0);dst.insert(0,('list',lemmas[key],a[2],not a[3]))
            width=var(12)
            return add(clock,width),add(motion,width if self.direction==1 else neg(width)),('list',key)
        assert a[0]=='run',('Opaque context reached',self.q,self.direction,a)
        w,d,q=table[self.q,a[1]]
        row=(self.q,a[1],w,d,q)
        if q==self.q and d==self.direction:
            src.pop(0);dst.insert(0,run(w,a[2]))
            return add(clock,a[2]),add(motion,a[2] if d==1 else neg(a[2])),('unary',row,a[2])
        assert a[2][0]>=1,('Unknown run may be empty',row,a)
        src[0]=run(a[1],minus1(a[2]))
        if d==self.direction:dst.insert(0,bit(w))
        else:src.insert(0,bit(w));self.direction=d
        self.q=q
        return add(clock,num(1)),add(motion,num(d)),('literal',row)


def prove_blocks(table):
    # These names merely identify entry states. Every theorem is rederived
    # from this exact literal table; failed derivation is fatal.
    signatures=[(64,1,'B','B'),(95,1,'B','C'),(40,-1,'B','B'),(97,-1,'C','B')]
    lemmas={};certificates=[];v=var(2)
    # Empty-list identity, and one-element identity with symbolic natural v.
    assert normal([bit(1)])==normal([bit(1)])
    assert normal(block(v,'C')+[bit(1)])==normal([bit(1)]+block(v,'B'))
    for q,d,before,after in signatures:
        L=('opaque','left');R=('opaque','right')
        if d==1:
            state=State(q,[L],block(v,before)+[R]);target=State(q,rev(block(v,after))+[L],[R])
        else:
            state=State(q,rev(block(v,before))+[L],[R],-1);target=State(q,[L],block(v,after)+[R],-1)
        steps=ZERO;motion=ZERO;trace=[]
        for _ in range(50):
            if state.key()==target.key():break
            steps,motion,event=state.step(table,{},steps,motion);trace.append(event)
        else:raise AssertionError(('One-block lemma did not close',q,d))
        assert steps==add(v,num(2))
        assert motion==(steps if d==1 else neg(steps))
        lemmas[q,d,before,d==-1]=after
        certificates.append({'entry':q,'direction':d,'before':before,'after':after,'steps':'v+2','arbitrary_contexts':True,'trace':trace})
    return lemmas,certificates


def file_bits(values,append=None):
    atoms=[]
    for v in values:atoms+=block(v)
    atoms+=block(var(11))+[tail()]
    if append is not None:atoms+=block(num(append))
    return atoms+[BLANK]

def case(table,lemmas,site,positive,append=1,keep_trace=False):
    pc,op,arg=site
    values=[var(2+i) for i in range(9)]
    if op=='CD':values[arg]=add(num(1),values[arg]) if positive else ZERO
    physical=[None]*9
    for i,j in enumerate(r.PHY):physical[j]=values[i]
    result=physical.copy();overflow=0;delta=0;extra=None
    if op=='CI':
        result[r.PHY[arg]]=add(result[r.PHY[arg]],num(1));successor,overflow=r.inc(pc);extra=append
    elif op=='CD' and positive:
        result[r.PHY[arg]]=minus1(result[r.PHY[arg]]);successor,overflow=r.inc(pc);delta=1
    elif op in ('CD','CB'):successor,overflow=r.inc(r.strip(pc,'0',arg if op=='CB' else 1))
    elif op=='CC':successor=r.strip(pc,'1',arg)
    elif op=='CH':successor=''
    else:raise AssertionError(site)
    state=State(96,[bit(1),BLANK],[bit(int(b)) for b in pc]+[run(0,add(var(1),num(64-len(pc)))),bit(1)]+file_bits(physical))
    target=State(96,[bit(1),BLANK],[bit(int(b)) for b in successor]+[run(0,add(var(1),num(64+delta+overflow-len(successor)))),bit(1)]+file_bits(result,extra))
    target_key=target.key();clock=ZERO;motion=ZERO;trace=[];rows=set();kinds={}
    for count in range(4000):
        key=state.key()
        if count and ((op=='CH' and state.q==254) or (op!='CH' and key==target_key)):
            assert nonnegative(clock) and clock[0]>0,('No positive progress',clock)
            if op!='CH':assert motion==num(-overflow),('Wrong head displacement',motion,overflow)
            return {'symbolic_steps':count,'duration':clock,'motion':motion,'rows':rows,'kinds':kinds,'trace':trace}
        clock,motion,event=state.step(table,lemmas,clock,motion)
        kinds[event[0]]=kinds.get(event[0],0)+1
        if event[0]!='list':rows.add(event[1][:2])
        if keep_trace:trace.append(event)
    raise AssertionError(('Symbolic proof did not close',site,positive,state.key(),target_key))


