#!/usr/bin/env python3
"""Bind every primitive instruction of GD, GDH, GDHS to arithmetic templates.

Adapted with attribution from the incoming AX11GH checker, itself adapted
from the updated AX11H packet. Checks ten entries and three AX operands,
explicit binder U(c,h), diagonal Gamma(d+x), ordinary h6, and three Shifts.

No Turing-machine simulator and no inherited source compiler are imported.
The handwritten companion proves the templates uniformly in iPRA.  This
program checks their finite instantiation, all source edges, the entire AX
expression, and representative exact-duration equations.  Finite tests are
not used in place of the companion's counter-induction arguments.
"""
from pathlib import Path
from itertools import product
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parent
N,T,W,A,D,H,X,Y,L=range(9)
TOKENS={'node49':['push'],'node55':['copyD'],'node58':['copyH'],
 'node70':['copyA'],'node65':['cons'],'node72':['readH'],
 'node75':['readDCons'],'node142':['copyGuard'],'node150':['compareGuard'],
 'node60':['incT']*2,'node61':['incT']*4}

def require(p,msg):
    if not p: raise AssertionError(msg)

def word(data):
    rules=data['rules']
    def expand(t,active=frozenset()):
        if isinstance(t,str):
            if t in TOKENS:return TOKENS[t]
            require(t in rules and t not in active,'invalid grammar reference')
            return expand(rules[t],active|{t})
        if t==['leaf','inc',1]:return ['incT']
        if t==['leaf','breakTo',1]:return ['close']
        require(isinstance(t,list) and len(t)==2,'unrecognized AX grammar token')
        return expand(t[0],active)+expand(t[1],active)
    return expand(data['root'])

class Templates:
    """Independent literal CFG templates; all ports are explicit integers."""
    def __init__(self): self.rows=[]; self.blocks=[]
    def emit(self,*row): self.rows.append(list(row))
    def mark(self,name,start): self.blocks.append(dict(kind=name,start=start,end=len(self.rows)))
    def inc(self,r): self.emit('inc',r,len(self.rows)+1)
    def jump(self,p): self.emit('jump',p)
    def clear(self,r):
        b=len(self.rows);self.emit('dec',r,b+2,b+1);self.jump(b);self.mark('clear',b)
    def transfer(self,r,s):
        b=len(self.rows);self.emit('dec',r,b+3,b+1);self.inc(s);self.jump(b)
        self.mark('transfer',b)
    def duplicate(self,r,s,t):
        b=len(self.rows);self.emit('dec',r,b+4,b+1);self.inc(s);self.inc(t);self.jump(b)
        self.mark('duplicate',b)
    def copy(self,r):
        b=len(self.rows);self.duplicate(r,T,X);self.transfer(X,r);self.mark('copy',b)
    def unpair(self,r):
        b=len(self.rows)
        for row in [('dec',r,b+8,b+1),('inc',Y,b+2),('dec',X,b+4,b+3),
                    ('jump',b+7),('dec',Y,b+7,b+5),('inc',X,b+6),
                    ('jump',b+4),('jump',b),('dec',Y,b+11,b+9),
                    ('inc',r,b+10),('jump',b+8)]: self.emit(*row)
        self.mark('unpair',b)
    def pair(self):
        b=len(self.rows)
        for row in [('dec',T,b+4,b+1),('inc',Y,b+2),('inc',X,b+3),
                    ('jump',b),('dec',X,b+10,b+5),('inc',Y,b+6),
                    ('dec',X,b+9,b+7),('inc',T,b+8),('jump',b+6),
                    ('jump',b)]: self.emit(*row)
        self.mark('pair',b)
    def times4(self):
        b=len(self.rows);self.emit('dec',Y,b+6,b+1)
        for _ in range(4):self.inc(T)
        self.jump(b);self.mark('times4',b)
    def compare(self,eq,ne):
        b=len(self.rows)
        for row in [('dec',H,b+4,b+1),('dec',X,b+3,b+2),('jump',b),
                    ('jump',b+5),('dec',X,eq,b+5),('dec',H,b+7,b+6),
                    ('jump',b+5),('dec',X,b+9,b+8),('jump',b+5),
                    ('jump',ne)]:self.emit(*row)
        self.mark('compare',b)
    def fetch_prefix(self):
        b=len(self.rows);self.emit('dec',L,b+2,b+1);self.jump(b+9)
        self.duplicate(N,L,X);self.inc(N)
        self.emit('dec',X,b+9,b+8);self.jump(b+6);self.mark('fetch_prefix',b)
    def atom(self,name):
        b=len(self.rows)
        if name=='incT':self.inc(T)
        elif name=='close':self.jump(3641)
        elif name=='push':
            self.transfer(T,X);self.transfer(W,T);self.pair();self.transfer(Y,W)
        elif name.startswith('copy') and name in ('copyD','copyH','copyA'):
            self.atom('push');self.copy({'copyD':D,'copyH':H,'copyA':A}[name])
        elif name=='cons':self.unpair(W);self.pair();self.times4()
        elif name=='readH':self.unpair(L);self.transfer(X,H)
        elif name=='readDCons':
            self.unpair(L);self.transfer(X,D);self.atom('copyD');self.atom('cons')
        elif name=='copyGuard':self.duplicate(A,Y,X)
        elif name=='compareGuard':
            self.compare(b+10,b+12);self.clear(T)
            self.transfer(Y,X);self.transfer(D,H)
            self.compare(b+28,b+30);self.clear(T)
        else:raise AssertionError(name)
        self.mark(name,b)

def full_templates(ww,variant='H'):
    require(variant in ('sum','H','HS'),'Shift variant')
    q=Templates();ports={}
    q.compare(10,11);q.emit('halt')
    q.unpair(W);q.transfer(X,H)
    ports['fetch']=len(q.rows);q.fetch_prefix()
    ports['decode']=len(q.rows);q.unpair(L);q.transfer(X,A)
    require(len(q.rows)==48,'prefix size')
    q.emit('dec',A,-1,49);q.emit('dec',A,-1,50)
    ports['AX']=len(q.rows)
    atom_ports=[]
    for token in ww:
        b=len(q.rows);q.atom(token);atom_ports.append(dict(token=token,start=b,end=len(q.rows)))
    ports['MP']=len(q.rows);require(ports['MP']==3554,'AX exit')
    q.atom('readDCons');q.transfer(T,X)
    ports['MP_compare']=len(q.rows);q.compare(-1,-1)
    ports['MP_success']=len(q.rows);q.copy(D)
    ports['return']=len(q.rows);q.jump(25)
    ports['Shift']=len(q.rows)
    if variant=='sum':
        q.transfer(T,X);q.duplicate(H,T,X);q.transfer(X,H);q.inc(X)
    elif variant=='H':q.clear(T);q.copy(H);q.inc(X)
    else:q.clear(T);q.duplicate(H,T,X);q.inc(H)
    q.jump(0)
    q.rows[48][2]=ports['Shift'];q.rows[49][2]=ports['MP']
    q.rows[ports['MP_compare']+4][2]=ports['MP_success']
    q.rows[ports['MP_compare']+9][1]=ports['return']
    require(ports=={'fetch':25,'decode':34,'AX':50,'MP':3554,'MP_compare':3624,
                    'MP_success':3634,'return':3641,'Shift':3642},'all command ports')
    require(len(q.rows)=={'sum':3654,'H':3653,'HS':3650}[variant],'source size')
    return q,ports,atom_ports

def pair(a,b):return (a+b)*(a+b+1)//2+b
def advance(a,b):return (a-1,b+1) if a else (b+1,0)
def unpair(n):
    # This bounded recursion is the definition used in the proof, not an
    # unbounded inverse search.  A faster inverse can replace it if proved.
    a=b=0
    for _ in range(n):a,b=advance(a,b)
    return a,b
def loop_cost(n):
    a=b=0;total=1
    for _ in range(n):
        total+=5 if a else 3*b+8
        a,b=advance(a,b)
    return total
def unpair_cost(n):return loop_cost(n)+3*unpair(n)[1]+1
def pair_cost(t,a):return 4*t+2+7*(a+t)*(a+t-1)//2+5*(a+t)
def compare_cost(h,x):
    if h==x:return 3*h+2
    if h<x:return 3*x+2
    return 2*h+x+4

class Arithmetic:
    """PR endpoints and exact clocks of the templates proved in the note."""
    def __init__(self,registers):self.r=list(registers);self.cost=0
    def inc(self,r):self.r[r]+=1;self.cost+=1
    def clear(self,r):self.cost+=2*self.r[r]+1;self.r[r]=0
    def transfer(self,r,s):
        self.cost+=3*self.r[r]+1;self.r[s]+=self.r[r];self.r[r]=0
    def duplicate(self,r,s,t):
        v=self.r[r];self.cost+=4*v+1;self.r[s]+=v;self.r[t]+=v;self.r[r]=0
    def copy(self,r):
        require(self.r[X]==0,'copy scratch precondition')
        self.duplicate(r,T,X);self.transfer(X,r)
    def unpair(self,r):
        require(self.r[X]==self.r[Y]==0,'unpair scratch precondition')
        a,b=unpair(self.r[r]);self.cost+=unpair_cost(self.r[r]);self.r[r]=b;self.r[X]=a
    def pair(self):
        require(self.r[Y]==0,'pair scratch precondition')
        t,a=self.r[T],self.r[X];self.cost+=pair_cost(t,a)
        self.r[T]=self.r[X]=0;self.r[Y]=pair(a,t)
    def times4(self):self.cost+=6*self.r[Y]+1;self.r[T]+=4*self.r[Y];self.r[Y]=0
    def compare(self):
        h,x=self.r[H],self.r[X];self.cost+=compare_cost(h,x);self.r[H]=self.r[X]=0
        return h==x
    def atom(self,name):
        if name=='incT':self.inc(T)
        elif name=='close':self.cost+=2 # closing break, then shared return jump
        elif name=='push':
            self.transfer(T,X);self.transfer(W,T);self.pair();self.transfer(Y,W)
        elif name in ('copyD','copyH','copyA'):
            self.atom('push');self.copy({'copyD':D,'copyH':H,'copyA':A}[name])
        elif name=='cons':self.unpair(W);self.pair();self.times4()
        elif name=='readH':self.unpair(L);self.transfer(X,H)
        elif name=='readDCons':
            self.unpair(L);self.transfer(X,D);self.atom('copyD');self.atom('cons')
        elif name=='copyGuard':self.duplicate(A,Y,X)
        elif name=='compareGuard':
            if self.compare():self.clear(T)
            self.transfer(Y,X);self.transfer(D,H)
            if self.compare():self.clear(T)
        else:raise AssertionError(name)
    def mp_tail(self):
        self.atom('readDCons');self.transfer(T,X)
        if self.compare():self.copy(D)
        self.cost+=1 # literal return jump to 25

def command_clock(ww,n,l,t,w,d,h,variant='H'):
    """Exact PR theta and terminal register file, for one scheduler step.

    This function may have enormous running time. Its primitive recursiveness,
    not practical evaluation on whole AX bodies, is the mathematical purpose.
    The accompanying certificate tests the finite body in a free algebra.
    """
    ar=Arithmetic([n,t,w,0,d,h,0,0,l])
    if l:ar.r[L]=l-1;ar.cost+=2
    else:ar.r[N]=n+1;ar.r[L]=n;ar.cost+=7*n+4
    ar.unpair(L);ar.transfer(X,A)
    if ar.r[A]==0:
        ar.cost+=1
        if variant=='sum':
            ar.transfer(T,X);ar.duplicate(H,T,X);ar.transfer(X,H);ar.inc(X)
        elif variant=='H':ar.clear(T);ar.copy(H);ar.inc(X)
        else:ar.clear(T);ar.duplicate(H,T,X);ar.inc(H)
        ar.cost+=1
        halt=ar.compare()
        if halt:ar.cost+=1;return ar.cost,'halt',ar.r
        ar.unpair(W);ar.transfer(X,H)
    elif ar.r[A]==1:
        ar.r[A]=0;ar.cost+=2;ar.mp_tail()
    else:
        ar.r[A]-=2;ar.cost+=2
        for token in ww:ar.atom(token)
    return ar.cost,25,ar.r

def literal_step(rows,pc,r):
    if pc=='halt':return pc,r
    z=rows[pc];r=list(r)
    if z[0]=='halt':return 'halt',r
    if z[0]=='jump':return z[1],r
    if z[0]=='inc':r[z[1]]+=1;return z[2],r
    if r[z[1]]==0:return z[2],r
    r[z[1]]-=1;return z[3],r

def step_exact(rows,pc,r,time):
    for _ in range(time):pc,r=literal_step(rows,pc,r)
    return pc,r

def local_duration_checks():
    count=0
    for token in ('push','copyD','copyH','copyA','cons','readH','readDCons','copyGuard','compareGuard','incT'):
        q=Templates();q.atom(token)
        for values in product(range(3),repeat=4):
            t,w,d,h=values;r=[7,t,w,2,d,h,0,0,5]
            if token=='compareGuard':r[X]=2;r[Y]=2;r[A]=0
            ar=Arithmetic(r);ar.atom(token)
            require(step_exact(q.rows,0,r,ar.cost)==(len(q.rows),ar.r),(token,values,ar.cost))
            count+=1
    for h,x in product(range(6),repeat=2):
        q=Templates();q.compare(10,11);r=[7,3,5,4,2,h,x,8,9]
        ar=Arithmetic(r);eq=ar.compare()
        require(step_exact(q.rows,0,r,ar.cost)==(10 if eq else 11,ar.r),('compare',h,x))
        count+=1
    for n,l in product(range(6),repeat=2):
        q=Templates();q.fetch_prefix();r=[n,4,5,0,2,3,0,0,l]
        out=list(r)
        if l:out[L]=l-1;cost=2
        else:out[N]=n+1;out[L]=n;cost=7*n+4
        require(step_exact(q.rows,0,r,cost)==(9,out),('fetch',n,l));count+=1
    return count

# Free arithmetic terms.  The normal form keeps scaled pairing as I.  Its
# interpretation is I(a,b)=4*p(a,b), including the alias I(0,0)=0.
Z=('zero',)
def su(a):return ('succ',a)
ONE=su(Z)
def add(a,b):return ('add',a,b)
def pp(a,b):return ('pair',a,b)
def ii(a,b):return ('I',a,b)
def mm(a,b):return su(ii(a,b))
def uu(a,b):return su(su(ii(b,a)))
def ee(a,b):return su(su(su(ii(a,b))))
def nn(a):return ii(a,ONE)
def conj(a,b):return nn(ii(a,nn(b)))
def ex(a,b):return nn(uu(a,nn(b)))
def hd(a):return a[1] if a[0]=='pair' else ('hd',a)
def tl(a):return a[2] if a[0]=='pair' else ('tl',a)
def cut(test,other,t):return ('zero_if_equal',test,other,t)

def symbolic_AX(ww,qfamily):
    n,t,w,a,d,h,x,y,tail=[('var',s)for s in('n','t','w','a','d','h','x','y','tail')]
    r=[n,t,w,a,d,h,Z,Z,pp(y,pp(x,tail))]
    def push():r[W]=pp(r[T],r[W]);r[T]=Z
    for index,token in enumerate(ww):
        if token=='compareGuard':
            require(r[A]==Z and r[X]==r[Y], 'symbolic comparison precondition')
            require(index>0 and ww[index-1]=='copyGuard', 'guard comparison predecessor')
        else:
            require(r[X]==r[Y]==Z, 'ordinary symbolic macro scratch precondition')
        if token=='incT':r[T]=su(r[T])
        elif token=='close':pass
        elif token=='push':push()
        elif token in ('copyD','copyH','copyA'):
            push();r[T]=r[{'copyD':D,'copyH':H,'copyA':A}[token]]
        elif token=='cons':r[T]=ii(hd(r[W]),r[T]);r[W]=tl(r[W])
        elif token=='readH':r[H]=add(r[H],hd(r[L]));r[L]=tl(r[L])
        elif token=='readDCons':
            r[D]=add(r[D],hd(r[L]));r[L]=tl(r[L]);r[T]=ii(r[T],r[D])
        elif token=='copyGuard':
            require(r[X]==r[Y]==Z,'symbolic guard scratch')
            r[X]=r[Y]=r[A];r[A]=Z
        elif token=='compareGuard':
            r[T]=cut(r[X],r[H],r[T]);r[H]=r[X]=Z
            r[X]=r[Y];r[Y]=Z;r[H]=r[D];r[D]=Z
            r[T]=cut(r[X],r[H],r[T]);r[H]=r[X]=Z
        else:raise AssertionError(token)
    dv,hv=add(d,x),add(h,y)
    heads=[ii(ex(dv,uu(dv,hv)),hv),ii(uu(dv,uu(a,hv)),uu(a,uu(dv,hv))),
           ii(mm(hv,dv),ii(ee(hv,a),mm(a,dv))),ii(ee(hv,dv),ii(mm(a,hv),mm(a,dv))),
           ex(dv,ee(hv,dv)),ii(uu(dv,a),ii(uu(dv,ii(a,hv)),uu(dv,hv)))]
    if qfamily:heads[5]=ii(uu(dv,ii(a,hv)),ii(uu(dv,a),uu(dv,hv)))
    rho=ii(ii(ii(hv,d),dv),ii(ii(dv,hv),ii(a,hv)))
    gamma=ii(dv,uu(dv,dv));point=ii(a,mm(a,dv));v=ii(mm(hv,dv),uu(a,mm(hv,dv)))
    ss=uu(dv,conj(ii(mm(hv,dv),point),ii(mm(a,dv),a)))
    qq=uu(a,ii(ss,nn(point)));gate=nn(ii(v,qq))
    guarded=cut(a,dv,cut(a,hv,gate))
    stack=w
    for term in [t,uu(a,h),rho]+heads+[gamma]:stack=pp(term,stack)
    expected=[n,guarded,stack,Z,Z,Z,Z,Z,tail]
    require(r==expected,'whole literal AX macro expression, both guards, scratch registers and residual field')
    return dict(status='PASS',AX_entries=10,AX_operands=3,all_registers_checked=True,
                all_intermediate_scratch_preconditions_checked=True,
                residual='tail',guard='a != H and a != D',Q=qfamily,explicit_binder='a',
                diagonal='Gamma(d+x)',outgoing_offset=0,closing_break=True)

def check_machine(path,out,variant='H'):
    require(variant in ('sum','H','HS'),'variant')
    tree=json.loads((path/'grammar.json').read_text());ww=word(tree)
    require(len(ww)==190,'macro-token count')
    require(ww[-3:]==['copyGuard','compareGuard','close'],'exact terminal guard/break composition')
    require(ww.count('copyGuard')==ww.count('compareGuard')==ww.count('close')==1,
            'unique guard and exit')
    templates,ports,ap=full_templates(ww,variant)
    ins=json.loads((path/'instructions.json').read_text())
    require(ins==templates.rows,'complete instruction/argument/zero-edge/positive-edge comparison')
    sites=json.loads((path/'sites.json').read_text())
    names=json.loads((path/'nodes.json').read_text())
    expanded=[]
    def expand(t,p=''):
        if isinstance(t,str):
            return expand(tree['root'] if t=='x67' else tree['rules'][t] if t in tree['rules'] else names[t],p)
        if t[0]=='leaf':expanded.append([p,t[1],t[2]]);return
        expand(t[0],p+'0');expand(t[1],p+'1')
    expand('node172');require(expanded==sites,'literal named-source expansion')
    interval={};indices={p:i for i,(p,_,_)in enumerate(sites)}
    def intervals(p):
        if p in indices:v=(indices[p],indices[p]+1)
        else:
            a,b=intervals(p+'0'),intervals(p+'1');require(a[1]==b[0],'source tree interval');v=(a[0],b[1])
        interval[p]=v;return v
    intervals('')
    def unwind(p,bit,k):
        while p:
            ch,p=p[-1],p[:-1]
            if ch==bit:
                k-=1
                if not k:return interval[p][1]%len(sites) if bit=='0' else interval[p][0]
        return 0
    graph=[]
    for i,(p,op,a)in enumerate(sites):
        after=(i+1)%len(sites)
        if op=='inc':row=['inc',a,after]
        elif op=='dec':row=['dec',a,unwind(p,'0',1),after]
        elif op=='breakTo':row=['jump',unwind(p,'0',a)]
        elif op=='continueTo':row=['jump',unwind(p,'1',a)]
        else:require(op=='halt','source opcode');row=['halt']
        graph.append(row)
    require(graph==ins,'independent full-tree CFG resolution')
    algebra=symbolic_AX(ww,False)
    duration_checks=local_duration_checks()
    command_checks=0
    for t,w,d,h in product(range(3),repeat=4):
        for tag in (0,1):
            seed=pair(tag,pair(1,0) if tag else 0)
            for fresh in (False,True):
                n,l=(seed,0) if fresh else (7,seed+1)
                cost,pc,r=command_clock(ww,n,l,t,w,d,h,variant)
                require(step_exact(ins,25,[n,t,w,0,d,h,0,0,l],cost)==(pc,r),'composed exact clock')
                command_checks+=1
    receipt=dict(status='PASS',family=path.name,source_sites=len(ins),
        shift_implementation={'sum':'compare t+h to 1','H':'compare h to 1','HS':'compare 1 to h'}[variant],
        all_instruction_rows_and_outgoing_edges_matched=True,
        named_source_expansion_checked=True,independent_tree_CFG_checked=True,
        macro_tokens=len(ww),ports=ports,primitive_templates=len(templates.blocks),
        algebra=algebra,local_exact_duration_tests=duration_checks,
        composed_shift_MP_duration_tests=command_checks,
        clock_definition='Arithmetic and command_clock in check_source.py',
        clock_proof='gd194_preservation.tex and inherited source_command_completion.tex; uniform QF-induction, not these tests',
        inputs={f:hashlib.sha256((path/f).read_bytes()).hexdigest()for f in
                ('instructions.json','sites.json','nodes.json','grammar.json')})
    if out is not None:
        out.mkdir(parents=True,exist_ok=True)
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        (out/'atom_ports.json').write_text(json.dumps(ap,indent=2)+'\n')
        (out/'template_ports.json').write_text(json.dumps(templates.blocks,indent=2)+'\n')
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--machine',type=Path,help='Single machine directory; default checks all three.')
    p.add_argument('--output',type=Path,help='Optional directory for fresh detailed certificates.')
    p.add_argument('--variant',choices=('sum','H','HS'),default='H')
    a=p.parse_args()
    if a.machine:results=[check_machine(a.machine,a.output,a.variant)]
    else:
        results=[check_machine(ROOT/'machines'/family,a.output/family if a.output else None,variant)
                 for family,variant in [('GD','sum'),('GDH','H'),('GDHS','HS')]]
    print(json.dumps(dict(status='PASS',machines=results),indent=2))
