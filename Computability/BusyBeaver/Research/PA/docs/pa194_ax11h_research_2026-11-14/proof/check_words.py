#!/usr/bin/env python3
"""Independent symbolic audit of AX11H command words.

The symbolic checks implement the displayed mathematical command equations.
They do not import the construction compiler, its arithmetic oracle, or the
literal TM simulator. They are an executable audit of universal algebraic
cases, not a proof-assistant theorem and not the missing PA/iPRA calibration.
"""
import argparse,hashlib,json
from pathlib import Path

def require(test,message):
    if not test: raise AssertionError(message)

def var(name): return ('variable',name)
def pair(a,b): return 0 if a==b==0 else ('pair',a,b)
def implication(a,b): return 0 if a==b==0 else ('I',a,b)
def universal(i,a): return ('U',i,a)
def membership(a,b): return ('M',a,b)
def equality(a,b): return ('E',a,b)
def negate(a): return implication(a,1)
def conjunction(a,b): return negate(implication(a,negate(b)))
def exists(i,a): return negate(universal(i,negate(a)))
def add(a,b):
    if a==0:return b
    if b==0:return a
    if type(a)==type(b)==int:return a+b
    return ('+',a,b)
def project(w):
    if w==0:return 0,0
    if isinstance(w,tuple) and w[0]=='pair':return w[1:]
    return ('hd',w),('tl',w)
def prepend(xs,w):
    for x in reversed(xs): w=pair(x,w)
    return w
def residue(x):
    if type(x)==int:return x%4
    return {'I':0,'U':2,'M':1,'E':3,'guarded_gate':0}.get(x[0])
def nonone(x,facts):
    if x in facts:return True
    if type(x)==int:return x!=1
    return residue(x) in (0,2,3)
def heads(D,H,c,d,h):
    I,U,M,E=implication,universal,membership,equality
    h1=I(exists(D,U(D,H)),H)
    h2=I(U(D,U(c,H)),U(c,U(D,H)))
    h3=I(M(H,D),I(E(H,c),M(c,D)))
    h4=I(E(H,D),I(M(c,H),M(c,D)))
    h5=exists(D,E(H,D))
    h6=I(U(D,c),I(U(D,I(c,H)),U(D,H)))
    rho=I(I(I(H,d),D),I(I(D,H),I(c,H)))
    gamma=I(c,U(c,c))
    # The guard chooses the inherited gate, an implication code, or 0.
    # Both alternatives have residue 0. Guard admissibility is a calculus rule.
    guarded=('guarded_gate',H,D,c)
    return [guarded,gamma,h6,h5,h4,h3,h2,h1,rho,U(d,h)]

SHIFT=('S',)
def AX(c=0,x=0,y=0,z=0):return ('A',c,x,y,z)
def MP(x=0):return ('M',x)
POP=[AX()]+[SHIFT]*12
PUSH=[AX()]+[SHIFT]*10+[MP()]
DISCARD=[MP()]

def run(word,store,not_one=frozenset(),trace=None):
    """Return None for a halt, otherwise the symbolic store.

    A symbolic guard must follow from residues or an explicit not-one
    hypothesis. Thus a silently assumed generic inequality cannot pass.
    """
    t,w,d,h=store
    for pos,cmd in enumerate(word):
        if trace is not None:trace.append({'position':pos,'command':cmd,'store':(t,w,d,h)})
        if cmd[0]=='S':
            if h==1:return None
            require(nonone(h,not_one),('unresolved cache-only guard',h))
            old_h=h
            h,w=project(w)
            t=old_h
            continue
        if cmd[0]=='A':
            c,x,y,z=cmd[1:];w=prepend(heads(add(d,x),add(h,y),c,d,h)+[t],w)
            t,d,h=0,z,0
        elif cmd[0]=='M':
            b=add(d,cmd[1]);goal=implication(t,b)
            if b==0:t,d,h=0,0,0
            elif goal==h:t,d,h=b,b,0
            elif t==h==0:
                # I(0,b)=0 iff b=0. Joining the b=0 / b>0 cases gives
                # the same visible result 0 with retained offset b.
                t,d,h=0,b,0
            elif residue(goal) is not None and residue(h) is not None and residue(goal)!=residue(h):
                t,d,h=0,b,0
            else:raise AssertionError(('unresolved MP comparison',goal,h))
        else:raise AssertionError(('invalid command',cmd))
    return t,w,d,h

def verify():
    t,w,d,h,a,b,c,D,H,u,x,i=map(var,('t','w','d','h','a','b','c','D','H','u','x','i'))
    checks=[]
    def ck(name,actual,expected):require(actual==expected,(name,actual,expected));checks.append(name)
    q=heads(d,h,c,d,h)
    ck('AX arbitrary fourth operand',run([AX(c,z=x)],(t,w,d,h)),(0,prepend(q+[t],w),x,0))
    ck('first ten Shifts',run([AX(c)]+[SHIFT]*10,(t,w,d,h)),(q[8],pair(t,w),0,q[9]))
    ck('first eleven Shifts',run([AX(c)]+[SHIFT]*11,(t,w,d,h)),(q[9],w,0,t))
    ck('Push arbitrary store',run(PUSH,(t,w,d,h)),(0,pair(t,w),0,0))
    ck('Push zero alias',run(PUSH,(0,0,d,h)),(0,0,0,0))
    ck('Pop non-one case',run(POP,(t,pair(a,w),d,h),{t}),(t,w,0,a))
    ck('Pop contradiction case',run(POP,(1,pair(a,w),d,h)),None)
    ck('Pop empty alias',run(POP,(t,0,d,h),{t}),(t,0,0,0))
    ck('Discard',run(DISCARD,(t,w,0,h)),(0,w,0,0))
    ck('Offset all natural indices',run([MP(i)],(0,w,0,0)),(0,w,i,0))
    for j in range(9):
        word=DISCARD+[AX(c,D,H)]+[SHIFT]*(j+2)+POP*(9-j)
        ck('selector '+str(j),run(word,(t,w,0,0)),(heads(D,H,c,0,0)[j],w,0,0))
    word=DISCARD+[MP(u),AX(c,x,H)]+[SHIFT]*10+POP
    ck('restricted rho with D=u+x',run(word,(t,w,0,0)),(heads(add(u,x),H,c,u,0)[8],w,0,0))
    gen=PUSH+[MP(i),SHIFT,AX(i)]+[SHIFT]*11
    ck('Generalization arbitrary formula',run(gen,(a,w,0,0)),(universal(i,a),w,0,0))
    ck('Generalization formula one',run(gen,(1,w,0,0)),(universal(i,1),w,0,0))
    ck('reserve zero',run(DISCARD+PUSH,(t,w,0,0)),(0,pair(0,w),0,0))
    suffix=[SHIFT,SHIFT,MP(b)]+POP
    ck('MP both non-one',run(suffix,(0,prepend([a,implication(a,b),0],w),0,0),{a,b}),(b,w,0,0))
    ck('MP antecedent one',run(suffix,(0,prepend([1,implication(1,b),0],w),0,0)),None)
    ck('MP consequent one',run([SHIFT,SHIFT,MP(1)]+POP,(0,prepend([a,implication(a,1),0],w),0,0),{a}),None)
    ck('MP all zero aliases',run([SHIFT,SHIFT,MP(0)]+POP,(0,0,0,0)),(0,0,0,0))
    ck('terminal Pop',run(POP,(1,w,0,0)),None)
    ck('plain Shift is NOT terminal test',run([SHIFT],(1,w,0,0)),(0,project(w)[1],0,project(w)[0]))
    ck('cached one halts even with top one',run([SHIFT],(1,w,0,1)),None)
    ck('AX resets arbitrary d,h',run([AX()],(t,w,d,h)),(0,prepend(heads(d,h,0,d,h)+[t],w),0,0))
    # Every symbolic guard split used by Pop and MP is an exhaustive decidable
    # equality split x=1 / x!=1. The listed cases cover arbitrary natural inputs.
    return {'status':'PASS','checks':checks,'checked_identities':len(checks),
            'shift_guard':'h=1','pop_cases':['t=1: halt','t!=1: (t,tail(w),0,head(w))'],
            'mp_suffix_cases':['a=1: halt','a!=1,b=1: halt','a!=1,b!=1: (b,w,0,0)'],
            'all_store_refuter':'AX(0,0,0,0); compile(refutation); Pop',
            'calibration_scope':'Relative to the explicit C4 numerical calculus; no unconditional iPRA/PA consistency calibration is established by this script.'}

def scheduler():
    c,x,y,z,tail=map(var,('c','x','y','z','tail'))
    code=pair(('plus_two',c),pair(y,pair(x,pair(z,tail))))
    tag,rest=project(code);yy,rest=project(rest);xx,rest=project(rest);zz,tt=project(rest)
    require((tag,xx,yy,zz,tt)==(('plus_two',c),x,y,z,tail),'four-operand decode')
    zero=pair(('plus_two',c),pair(0,pair(0,pair(0,0))))
    tag,rest=project(zero)
    for k in range(3):head,rest=project(rest);require(head==0,'zero operand decode')
    require(rest==0,'zero continuation decode')
    return {'four_operands':True,'order':'c in tag, then y,x,z','total_zero_projections':True,
            'cofinal_raw_candidates':'p(k+2,p(0,p(0,p(0,e(refuter)))))',
            'proof_obligation':'Components are bounded by their Cantor pair; e(nonempty)=1+raw supplies strict continuation decrease.'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=verify();result['scheduler']=scheduler();result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
