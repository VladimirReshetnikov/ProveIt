"""A transparent, complete first-order reference interface for EPSC.

This checker uses genuine falsity and explicitly checked capture-avoiding
universal instantiation. It is not the 248-state reduced calculus and is not
a state-minimized implementation. Every proof line is constructed by a rule;
there are no assumptions, arbitrary conclusions, or admitted axioms.
"""
import argparse, json

BOT=('bot',)
def Mem(i,j): return ('mem',nat(i),nat(j))
def Imp(a,b): return ('imp',a,b)
def All(i,a): return ('all',nat(i),a)
def Not(a): return Imp(a,BOT)
def And(a,b): return Not(Imp(a,Not(b)))
def Or(a,b): return Imp(Not(a),b)
def Ex(i,a): return Not(All(i,Not(a)))
def nat(x):
    if type(x) is not int or x<0:raise ValueError('natural label required')
    return x

def formula(x):
    if not isinstance(x,(list,tuple)) or not x:raise ValueError('formula array required')
    op=x[0]
    if op=='bot' and len(x)==1:return BOT
    if op=='mem' and len(x)==3:return Mem(x[1],x[2])
    if op=='imp' and len(x)==3:return Imp(formula(x[1]),formula(x[2]))
    if op=='all' and len(x)==3:return All(x[1],formula(x[2]))
    raise ValueError('malformed formula')

def labels(a):
    if a==BOT:return set()
    if a[0]=='mem':return {a[1],a[2]}
    if a[0]=='imp':return labels(a[1])|labels(a[2])
    return {a[1]}|labels(a[2])

def free(a):
    if a==BOT:return set()
    if a[0]=='mem':return {a[1],a[2]}
    if a[0]=='imp':return free(a[1])|free(a[2])
    return free(a[2])-{a[1]}

def fresh(*sets):return max(set().union(*sets),default=-1)+1

def replace_free(a,mapping):
    """Simultaneous variable replacement with alpha-renaming when required."""
    if a==BOT:return a
    if a[0]=='mem':return Mem(mapping.get(a[1],a[1]),mapping.get(a[2],a[2]))
    if a[0]=='imp':return Imp(replace_free(a[1],mapping),replace_free(a[2],mapping))
    v,body=a[1],a[2]
    active={x:y for x,y in mapping.items() if x!=v and x in free(body)}
    if v in active.values():
        w=fresh(labels(body),set(active),set(active.values()),{v})
        body=replace_free(body,{v:w})
        v=w
    return All(v,replace_free(body,active))

def close(a):
    for v in sorted(free(a),reverse=True):a=All(v,a)
    return a

def epsc(matrix):
    matrix=formula(matrix)
    k=fresh(labels(matrix))
    x,y,b,c,z=range(k,k+5)
    rho=replace_free(matrix,{0:x,1:y})
    subset=All(z,Imp(Mem(z,y),Mem(z,b)))
    bounded=All(x,Ex(b,All(y,Imp(rho,subset))))
    empty=All(z,Not(Mem(z,x)))
    closed=All(x,All(y,Imp(And(Or(empty,Mem(x,c)),rho),Mem(y,c))))
    support=All(y,Imp(Mem(y,c),Ex(x,rho)))
    return close(Imp(bounded,Ex(c,And(closed,support))))

def check(records,allow_ir=False):
    if not isinstance(records,list) or not records:raise ValueError('nonempty proof required')
    lines=[]
    def previous(i):
        nat(i)
        if i>=len(lines):raise ValueError('proof reference must point backward')
        return lines[i]
    for rec in records:
        if not isinstance(rec,list) or not rec:raise ValueError('proof record required')
        op,args=rec[0],rec[1:]
        if op=='K' and len(args)==2:
            a,b=map(formula,args);out=Imp(a,Imp(b,a))
        elif op=='S' and len(args)==3:
            a,b,c=map(formula,args);out=Imp(Imp(a,Imp(b,c)),Imp(Imp(a,b),Imp(a,c)))
        elif op=='C' and len(args)==2:
            a,b=map(formula,args);out=Imp(Imp(Not(a),Not(b)),Imp(b,a))
        elif op=='UI' and len(args)==3:
            x,y,a=nat(args[0]),nat(args[1]),formula(args[2])
            out=Imp(All(x,a),replace_free(a,{x:y}))
        elif op=='QD' and len(args)==3:
            x,a,b=nat(args[0]),formula(args[1]),formula(args[2])
            if x in free(a):raise ValueError('QD variable is free in antecedent')
            out=Imp(All(x,Imp(a,b)),Imp(a,All(x,b)))
        elif op=='GEN' and len(args)==2:out=All(nat(args[0]),previous(args[1]))
        elif op=='MP' and len(args)==2:
            a,p=previous(args[0]),previous(args[1])
            if p[0]!='imp' or p[1]!=a:raise ValueError('MP antecedent mismatch')
            out=p[2]
        elif op=='EPSC' and len(args)==1:out=epsc(args[0])
        elif op=='IR' and not args and allow_ir:out=All(0,Not(Mem(0,0)))
        else:raise ValueError('unknown, disabled or malformed rule')
        lines.append(out)
    return {'valid':True,'refutation':lines[-1]==BOT,'lines':len(lines),'conclusion':lines[-1]}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate');ap.add_argument('--ir',action='store_true')
    args=ap.parse_args()
    with open(args.certificate) as f:records=json.load(f)
    try:print(json.dumps(check(records,args.ir),indent=2))
    except ValueError as exc:
        print(json.dumps({'valid':False,'error':str(exc)}));raise SystemExit(1)

if __name__=='__main__':main()
