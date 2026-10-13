from pathlib import Path
import mpmath as mp
import json, math
from fractions import Fraction
BASE=Path(__file__).parent
mp.mp.dps=75

def p(n,y):
    if n==0:return mp.mpf(0)
    return sum((-1)**k*math.comb(n,2*k+1)*mp.pi**(2*k)*y**(n-2*k-1) for k in range((n-1)//2+1))

def pv_reconstruct(nodes,weights,n,dps=75,T=135):
    with mp.workdps(dps):
        rational_a=list(map(Fraction,nodes)); a=[mp.mpf(q.numerator)/q.denominator for q in rational_a]; c=list(map(mp.mpf,weights)); rational_poles={}; shifted=[]
        for aj,cj in zip(rational_a,c):
            N=max(0,(-aj.numerator)//aj.denominator+1)
            qq=aj+N; shifted.append(mp.mpf(qq.numerator)/qq.denominator)
            for k in range(N):
                b=-aj-k; rational_poles[b]=rational_poles.get(b,mp.mpf(0))+cj
        poles={mp.mpf(b.numerator)/b.denominator:r for b,r in rational_poles.items() if r}
        pp=sorted(poles)
        def g(x):return -sum(cj*mp.digamma(x+aj) for cj,aj in zip(c,shifted))
        d0=-sum(cj*mp.digamma(aj) for cj,aj in zip(c,a))
        widths={b:min([b/4,mp.mpf('.17')]+[abs(b-bb)/4 for bb in pp if bb!=b]) for b in pp}
        def w(x):return p(n,mp.log(x))/x
        def fun(t):
            x=mp.exp(t); cut=d0 if t<0 else 0
            active=next((b for b in pp if abs(x-b)<widths[b]),None)
            if active is None:
                return p(n,t)*(g(x)+sum(r/(x-b) for b,r in poles.items())-cut)
            b=active;r=poles[b]
            if x==b:
                divided=(n*p(n-1,mp.log(b))-p(n,mp.log(b)))/b**2
            else:
                divided=(w(x)-w(b))/(x-b)
            return x*(r*divided+w(x)*(g(x)+sum(rr/(x-bb) for bb,rr in poles.items() if bb!=b)-cut))
        # Symmetric subtraction is in x, not t; its exact PV integral is zero.
        edges=sorted(set([-mp.mpf(T),-40,-12,-4,-1,mp.mpf(0),1,4,12,40,mp.mpf(T)]+[mp.log(b+sg*widths[b]) for b in pp for sg in [-1,1]]+[mp.log(b) for b in pp]))
        value=sum(mp.quad(fun,[l,r]) for l,r in zip(edges,edges[1:]))
        correction=((-1)**(n//2)*mp.pi**n*d0/(n+1)) if n%2==0 else 0
        imag=-mp.pi*sum(r*p(n,mp.log(b))/b for b,r in poles.items())
        reconstructed=value+correction+1j*imag
        reference=sum(cj*mp.stieltjes(n,aj) for cj,aj in zip(c,shifted))-sum(r*(mp.log(b)+1j*mp.pi)**n/b for b,r in poles.items())
        return {'nodes':nodes,'weights':weights,'n':n,'dps':dps,'log_cutoff':T,'upper_integral':mp.nstr(reconstructed,55),'upper_hurwitz_shift_reference':mp.nstr(reference,55),'absolute_error':mp.nstr(abs(reconstructed-reference),8),'PV_integral':mp.nstr(value,50),'residue_imaginary_part':mp.nstr(imag,50)}

rows=[]
for a,c in [(['-.4','1.3'],['1','-1']),(['-1.4','.7'],['1','-1']),(['-1.4','-.4','.6'],['1','-2','1'])]:
    for n in [1,2,3]:
        r=pv_reconstruct(a,c,n)
        assert mp.mpf(r['absolute_error'])<mp.mpf('1e-43'),r
        rows.append(r);print('PV',a,n,r['absolute_error'],flush=True)
# Independent precision/cutoff refinement of one nonrational multiple-pole case.
refinement=pv_reconstruct(['-1.4','.7'],['1','-1'],3,dps=95,T=165)
assert mp.mpf(refinement['absolute_error'])<mp.mpf('1e-53')
print('refinement',refinement['absolute_error'],flush=True)
# Direct ordinary integrals of the cut kernel, independently of beta formulas.
beta=[]
for b,s,v in [('0.4','.7','.3'),('1.4','.8','.5'),('.6','.6','.2')]:
    b,s,v=map(mp.mpf,(b,s,v))
    for sign in [1,-1]:
        left=mp.e**(-sign*1j*mp.pi*s)*mp.quad(lambda t:t**(v-1)*(1-t)**(-s),[0,.5,1])*b**(v-s)
        # Map the x>b piece to t in(0,1); ordinary beta-integral quadrature.
        right=mp.quad(lambda t:t**(-s)*(1-t)**(s-v-1),[0,.5,1])*b**(v-s)
        ref=mp.e**(sign*1j*mp.pi*(v-s))*b**(v-s)*mp.gamma(v)*mp.gamma(s-v)/mp.gamma(s)
        err=abs(left+right-ref)
        assert err<mp.mpf('1e-13'),(b,s,v,err)
        beta.append({'b':str(b),'s':str(s),'v':str(v),'bank':sign,'ordinary_quadrature_error':mp.nstr(err,8)})
        print('beta',b,s,v,sign,mp.nstr(err,8),flush=True)
# Sign/contact negative controls use actual evaluated formulas.
controls={
 'reverse_upper_residue_sign':abs(mp.mpf(rows[0]['residue_imaginary_part']))>mp.mpf('1'),
 'omit_even_origin_constant':abs(mp.pi**2*(-mp.digamma(mp.mpf('-.4'))+mp.digamma(mp.mpf('1.3')))/3)>mp.mpf('.1'),
 'omit_a_crossed_pole':abs(mp.pi/mp.mpf('1.4'))>mp.mpf('1'),
}
assert all(controls.values())
out={'status':'PASS','PV_reconstruction_checks':rows,'precision_refinement':refinement,'ordinary_beta_cut_integrals':beta,'negative_controls':controls,'scope':'Finite floating-point diagnostics, not interval certificates. All-index and boundary-limit proofs are in contour-stieltjes.tex. Original PV computed by symmetric local x-subtractions; reference uses independent Hurwitz shift plus positive-node Stieltjes values.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',flush=True)
