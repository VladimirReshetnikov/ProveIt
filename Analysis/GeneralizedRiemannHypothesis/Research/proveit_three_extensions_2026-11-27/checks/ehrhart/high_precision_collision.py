#!/usr/bin/env python3
"""80-decimal arithmetic cross-check of selected local Ehrhart collisions.
This uses the exact recurrences with mpmath arithmetic; values remain numerical.
"""
import json,pathlib
import mpmath as mp
mp.mp.dps=80

def eval_mp(d,t):
    hp=(mp.mpf(1),mp.mpf(0),mp.mpf(0));hc=(2*t,mp.mpf(2),mp.mpf(0))
    cp=hp;cc=hc
    for n in range(1,d):
        A=mp.mpf(2*(2*n+1))/(n+1)**2;B=mp.mpf(n*n)/(n+1)**2
        hn=(A*t*hc[0]-B*hp[0],A*(hc[0]+t*hc[1])-B*hp[1],A*(2*hc[1]+t*hc[2])-B*hp[2])
        a=mp.mpf(2)/(n+1);b=mp.mpf(n)/(n+1)
        cn=(a*t*cc[0]-b*cp[0],a*(cc[0]+t*cc[1])-b*cp[1],a*(2*cc[1]+t*cc[2])-b*cp[2])
        if n==d-1:
            D=((2*t*cc[0]+cp[0])/(2*d),(2*cc[0]+2*t*cc[1]+cp[1])/(2*d),(4*cc[1]+2*t*cc[2]+cp[2])/(2*d))
        hp,hc=hc,hn;cp,cc=cc,cn
    return hc,D

def main():
    out=[]
    for d,guess in [(100,'0.4923790216264995'),(101,'0.40003794630614053'),(1000,'0.35289979877893685'),(1001,'0.2906552097578934')]:
        def f(t):
            H,D=eval_mp(d,t);return H[1]*D[0]-H[0]*D[1]
        def fp(t):
            H,D=eval_mp(d,t);return H[2]*D[0]-H[0]*D[2]
        root=mp.findroot(f,mp.mpf(guess),df=fp,solver='newton',tol=mp.mpf('1e-70'))
        H,D=eval_mp(d,root);M=H[0]/D[0]
        row={'d':d,'collision_height':mp.nstr(root,65),'collision_M':mp.nstr(M,65),'W_residual':mp.nstr(f(root),8),'digits_of_working_precision':mp.mp.dps,'scope':'high-precision illustration, not an interval certificate'}
        out.append(row);print(json.dumps(row),flush=True)
    pathlib.Path(__file__).with_name('high_precision_collisions.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
