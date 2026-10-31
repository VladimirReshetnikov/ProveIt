"""Exact Pell-only m=3 example; it makes no factor-unit or full-zero claim."""
import json

def pell(n, a):
    x,y=1,0
    D=(a+1)*(a+3)
    for _ in range(n):
        x,y=(a+2)*x+D*y,x+(a+2)*y
    assert x*x==1+D*y*y
    return x,y

q,Y,X,n,m,eta,zeta=2,8,14,2,3,2159,5013
Q=X*Y*Y
B=2*(Q-1)+1
a=X*Y+Y
k=eta+zeta
first,first_y=pell(n,B)
main,main_y=pell(m,a)
assert Y==q**3 and eta>0 and zeta>0 and 2*first_y==k
assert main_y==eta+Y*k and n<m<6
print(json.dumps({'q':q,'Y':Y,'X':X,'n':n,'m':m,'eta':eta,'zeta':zeta,
                  'Q':Q,'B':B,'k':k,'a':a,'c':main_y,
                  'first':first,'main':main},sort_keys=True,indent=2))
