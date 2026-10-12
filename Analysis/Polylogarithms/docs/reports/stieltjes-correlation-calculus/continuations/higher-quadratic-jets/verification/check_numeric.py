#!/usr/bin/env python3
"""Independent high-precision diagnostics, explicitly not rigorous enclosures."""
from __future__ import annotations
import argparse,json,platform,time,subprocess,sys,tempfile
from pathlib import Path
import mpmath as mp
from core import *

def main(out,part):
    mp.mp.dps=50
    rows=[];start=time.time()
    def test(name,lhs,rhs):
        error=abs(lhs-rhs); scaled=error/max(mp.mpf(1),abs(lhs),abs(rhs))
        if scaled>=mp.mpf('1e-34'):
            raise AssertionError(f'{name}: scaled error {mp.nstr(scaled,12)}; lhs={lhs}; rhs={rhs}')
        rows.append({'name':name,'lhs':str(lhs),'rhs':str(rhs),'absolute_error':mp.nstr(error,12),'scaled_error':mp.nstr(scaled,12)})
        print(name,mp.nstr(scaled,4),flush=True)
    if part in ('all','factorization'):
        a,b=mp.mpf('.8'),mp.mpf('.12')
        for d in range(4):
            W=[0]*d+[1]
            for r in range(1,4):
                test(f'factorization_d{d}_r{r}',delta_jet(a,b,W,r,head=0),separate_delta_jet(a,b,d,r))
        for a,b in [(mp.mpf('.7'),mp.mpf('.4')),(mp.mpf('.35'),mp.mpf('1.7'))]:
            h=2j*b;d=-1j*b
            integral=2*h*mp.quad(lambda t:mp.digamma(a+d+h*t)*mp.log(t/(1-t)),[0,.5,1])
            test(f'digamma_logsquare_a{a}_b{b}',delta_jet(a,b,[1],2),integral)
            test(f'head_invariance_a{a}_b{b}',delta_jet(a,b,[1,2,-1],3),delta_jet(a,b,[1,2,-1],3,head=int(mp.ceil(3*b))+5))
        a0,a1,c,d=map(mp.mpf,('.7','1.4','.3','.05'));h=c-d
        ga=2*h*mp.quad(lambda t:(mp.loggamma(a1+d+h*t)-mp.loggamma(a0+d+h*t))*mp.log(t/(1-t)),[0,.5,1])
        series=mp.mpf(0)
        for r in range(2,150):
            gap=(mp.digamma(a1+d)-mp.digamma(a0+d)) if r==2 else (mp.zeta(r-1,a0+d)-mp.zeta(r-1,a1+d))/(r-1)
            series+=2*(-1)**r*mp.harmonic(r-1)*h**r/r*gap
        test('Gamma_anchored_primitive',ga,series)
        for y,h in [(mp.mpf('.8'),mp.mpf('.3')),(mp.mpf('2'),mp.mpf('1.1'))]:
            f=lambda yy:yy*mp.log1p(h/yy)**2-2*h*mp.polylog(2,h/(yy+h))
            test(f'dilog_primitive_y{y}',mp.diff(f,y),mp.log1p(h/y)**2)
    if part in ('all','fourier'):
        for m in range(7):
            for x in map(mp.mpf,('.7','2.3')):
                P,A,B=pab(m)
                rhs=mp.sqrt(mp.pi/(2*x))*mp.exp(-x)*(peval(A,1/x)*mp.exp(2*x)*mp.e1(2*x)+peval(B,1/x))
                test(f'Bessel_order_m{m}_x{x}',mp.diff(lambda nu:mp.besselk(nu,x),m+mp.mpf('.5')),rhs)
        for p in (1,2,3):
            test(f'J_integral_series_p{p}',j_integral(p,mp.mpf('.29'),mp.mpf('.6')),j_series(p,mp.mpf('.29'),mp.mpf('.6')))
        for m in range(4):
            test(f'second_jet_m{m}',second_fourier(m,'.37','.09'),second_binomial(m,'.37','.09'))
        def L(m,a,u):
            b=mp.sqrt(u);q=mp.exp(-2*mp.pi*b+2j*mp.pi*a)
            zero=-2**(2*m+1)*mp.factorial(m)**2*mp.pi*b**(2*m+1)/mp.factorial(2*m+1)
            return zero+2*(-1)**m*mp.factorial(m)*mp.fsum(mp.factorial(m+j)*b**(m-j)*mp.re(mp.polylog(m+j+1,q))/(mp.factorial(j)*mp.factorial(m-j)*4**j*mp.pi**(m+j)) for j in range(m+1))
        for m in (1,2,3):
            a,u=mp.mpf('.31'),mp.mpf('.21')
            def corrected(mm,uu): return second_fourier(mm,a,mp.sqrt(uu))+2*mp.harmonic(mm)*L(mm,a,uu)
            test(f'Appell_second_m{m}',mp.diff(lambda uu:corrected(m,uu),u),m*corrected(m-1,u))
    if part in ('all','collision'):
        a,u,v=map(mp.mpf,('.31','.8','.17'))
        for P in ([1],[0,1],[0,0,1],[2,-3,1],[0,0,0,1]):
            test(f'collision_sum_integral_P{P}',k_sum(a,u,v,P),k_integral(a,u,v,P))
        for N in range(1,6):
            test(f'positive_resolvent_N{N}',e_integer(N,a,u),(-1)**(N-1)*mp.diff(lambda t:e1_resolvent(a,t),u,N-1)/mp.factorial(N-1))
        for P in ([1],[1,-2,1],[0,0,0,1]):
            h=mp.mpf('.015')
            test(f'collision_Taylor_P{P}',k_sum(a,u+h,u,P),k_collision_series(a,u,h,P,terms=38))
            confluent=p_derivative_at(P,-u,0)*e_integer(2,a,u)+p_derivative_at(P,-u,1)*e_integer(1,a,u)
            test(f'collision_confluent_P{P}',confluent,-mp.diff(lambda t:peval(P,-t)*e1_resolvent(a,t),u))
        for P in ([1],[0,1],[1,-2,1]):
            aa,uu,vv=map(mp.mpf,('.37','.0081','.0036'))
            rhs=2*mp.fsum(p_derivative_at(P,-t,l)/mp.factorial(l)*second_fourier(l,aa,mp.sqrt(t))
                          for t in (uu,vv) for l in range(len(P)))-k_sum(aa,uu,vv,P)
            test(f'product_second_independent_P{P}',product_second_binomial(aa,uu,vv,P),rhs)
        b,c=mp.mpf('1.1'),mp.mpf('.45')
        mean=2*mp.quad(lambda x:mp.log((x*x+b*b)/(x*x+c*c))**2,[0,1,3,mp.inf])
        exact=8*mp.pi*(b*mp.log(2*b)+c*mp.log(2*c)-(b+c)*mp.log(b+c))
        test('averaged_logsquare',mean,exact)
    report={'status':'passed','part':part,'decimal_working_precision':50,'scaled_tolerance':'1e-34','comparisons':len(rows),
            'maximum_scaled_error':max((mp.mpf(r['scaled_error']) for r in rows),default=mp.mpf(0)),
            'results':rows,'python':platform.python_version(),'mpmath':mp.__version__,'elapsed_seconds':round(time.time()-start,3),
            'scope':'Floating-point diagnostics. Not interval certificates and not substitutes for proofs.'}
    report['maximum_scaled_error']=mp.nstr(report['maximum_scaled_error'],12)
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS {len(rows)} comparisons -> {out}',flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--part',choices=['all','factorization','fourier','collision'],default='all')
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'numerical_results.json')
    args=ap.parse_args()
    if args.part != 'all':
        main(args.output,args.part)
    else:
        # Isolate special-function caches and working-precision state by suite.
        reports=[]
        with tempfile.TemporaryDirectory(prefix='hqj-replay-') as td:
            for part in ('factorization','fourier','collision'):
                target=Path(td)/(part+'.json')
                subprocess.run([sys.executable,str(Path(__file__).resolve()),'--part',part,'--output',str(target)],check=True)
                reports.append(json.loads(target.read_text()))
        merged={'status':'passed','part':'all (three isolated processes)',
                'comparisons':sum(r['comparisons'] for r in reports),
                'decimal_working_precision':50,'scaled_tolerance':'1e-34',
                'results':[row for report in reports for row in report['results']],
                'parts':{r['part']:r['comparisons'] for r in reports},
                'scope':'Floating-point diagnostics, not interval certificates.'}
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(merged,indent=2)+'\n')
        print(f"PASS {merged['comparisons']} comparisons in three isolated processes -> {args.output}")
