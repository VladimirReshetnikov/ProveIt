from pathlib import Path
import json
N,T,W,A,D,H,X,Y,L=range(9)
def require(a,m):
 if not a:raise AssertionError(m)
TOKENS={'node49':['push'],'node55':['copyD'],'node58':['copyH'],'node70':['copyA'],'node65':['cons'],'node72':['readH'],'node75':['readDCons'],'node142':['copyGuard'],'node150':['compareGuard'],'node60':['incT']*2,'node61':['incT']*3,'nodeDouble':['doubleT']}
def word(t):
 if isinstance(t,str):return TOKENS[t]
 if t==['leaf','inc',1]:return ['incT']
 return word(t[0])+word(t[1])
# Free arithmetic terms.  The normal form keeps scaled pairing as I.  Its
# interpretation is I(a,b)=3*p(a,b), including the alias I(0,0)=0.
Z=('zero',)
def su(a):return ('succ',a)
ONE=su(Z)
def add(a,b):return ('add',a,b)
def pp(a,b):return ('pair',a,b)
def ii(a,b):return ('I',a,b)
def double(a):return ('double',a)
def mm(a,b):return su(ii(a,double(b)))
def uu(a,b):return su(su(ii(b,a)))
def ee(a,b):return su(ii(a,su(double(b))))
def nn(a):return ii(a,ONE)
def conj(a,b):return nn(ii(a,nn(b)))
def ex(a,b):return nn(uu(a,nn(b)))
def hd(a):return a[1] if a[0]=='pair' else ('hd',a)
def tl(a):return a[2] if a[0]=='pair' else ('tl',a)
def cut(test,other,t):return ('zero_if_equal',test,other,t)

def symbolic_AX(ww,qfamily):
    n,t,w,a,d,h,x,y,z,tail=[('var',s)for s in('n','t','w','a','d','h','x','y','z','tail')]
    r=[n,t,w,a,d,h,Z,Z,pp(y,pp(x,pp(z,tail)))]
    def push():r[W]=pp(r[T],r[W]);r[T]=Z
    for index,token in enumerate(ww):
        if token=='compareGuard':
            require(r[A]==Z and r[X]==r[Y], 'symbolic comparison precondition')
            require(index>0 and ww[index-1]=='copyGuard', 'guard comparison predecessor')
        else:
            require(r[X]==r[Y]==Z, 'ordinary symbolic macro scratch precondition')
        if token=='incT':r[T]=su(r[T])
        elif token=='doubleT':r[T]=double(r[T])
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
    gamma=ii(a,uu(a,a));point=ii(a,mm(a,dv));v=ii(mm(hv,dv),uu(a,mm(hv,dv)))
    ss=uu(dv,conj(ii(mm(hv,dv),point),ii(mm(a,dv),a)))
    qq=uu(a,ii(ss,nn(point)));gate=nn(ii(v,qq))
    guarded=cut(a,dv,cut(a,hv,gate))
    stack=w
    for term in [t,uu(a,h),rho]+heads+[gamma,guarded]:stack=pp(term,stack)
    expected=[n,Z,stack,Z,Z,Z,Z,Z,pp(z,tail)]
    require(r==expected,'whole literal AX macro expression, both guards, scratch registers and residual field')
    return dict(status='PASS',AX_entries=11,all_registers_checked=True,
                all_intermediate_scratch_preconditions_checked=True,
                residual='p(z,tail)',guard='a != H and a != D',Q=qfamily,explicit_binder='a')


if __name__=='__main__':
 p=Path(__file__).resolve().parent
 w=word(json.loads((p/'grammar.tree.json').read_text()))
 receipt=symbolic_AX(w,True)
 receipt['syntax']='I=3p; U=3p(body,binder)+2; M=3p(a,2b)+1; E=3p(a,2b+1)+1'
 receipt['tokens']=len(w)
 (p/'algebra_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
