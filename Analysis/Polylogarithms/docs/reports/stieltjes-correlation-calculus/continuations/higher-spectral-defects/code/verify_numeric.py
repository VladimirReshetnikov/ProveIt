#!/usr/bin/env python3
"""High-precision diagnostics, not interval or validated-tail certificates.
Pochhammer-Hurwitz routes share mpmath's zeta implementation. Gamma
integrals, ordinary sums and beta integrals give additional cross-checks.
"""
from pathlib import Path
from collections import Counter
import argparse, json, platform, time
from spectral_defects import *
ROOT=Path(__file__).resolve().parents[1]
records=[]
def done(group,label):
    return any(r['group']==group and r['label']==label and r['pass'] for r in records)
def compare(group,label,lhs,rhs,tol):
    error=abs(lhs-rhs)/max(mp.mpf(1),abs(lhs),abs(rhs))
    row={'group':group,'label':label,'lhs':mp.nstr(lhs,45),'rhs':mp.nstr(rhs,45),
         'scaled_residual':mp.nstr(error,12),'pass':bool(error<tol)}
    if done(group,label): return
    records.append(row)
    (ROOT/'results'/'numeric_checkpoint.json').write_text(json.dumps(records,indent=2)+'\n')
    if not row['pass']:
        print('FAILED',json.dumps(row),flush=True)
        raise AssertionError(label)
def integer_series(k,a,b,w,terms=80):
    assert b<a
    return mp.fsum(wd*mp.rf(k,n)/mp.factorial(n)*(-b*b)**n*mp.zeta(2*k+2*n-d,a)
                  for d,wd in enumerate(w) if wd for n in range(terms))
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dps',type=int,default=35)
    ap.add_argument('--quick',action='store_true',help='Skip logarithmic-beta and degree-four covariance checks')
    ap.add_argument('--resume',action='store_true',help='Resume an interrupted run at the same precision/profile')
    ar=ap.parse_args()
    if ar.dps<35:ap.error('Use at least 35 digits')
    terms=80; nodes=56
    profile={'dps':ar.dps,'terms':terms,'Gauss_nodes':nodes,'quick':ar.quick}
    profile_path=ROOT/'results'/'numeric_checkpoint_profile.json'
    (ROOT/'results').mkdir(exist_ok=True)
    if ar.resume:
        if not profile_path.exists():
            ap.error('Checkpoint profile is missing; start a fresh run without --resume.')
        saved_profile=json.loads(profile_path.read_text())
        if saved_profile != profile:
            ap.error('Checkpoint profile differs from this run; use the original options or omit --resume.')
        checkpoint=ROOT/'results'/'numeric_checkpoint.json'
        if not checkpoint.exists():ap.error('No numerical checkpoint exists.')
        records.extend(json.loads(checkpoint.read_text()))
    else:
        profile_path.write_text(json.dumps(profile,indent=2)+'\n')
        (ROOT/'results'/'numeric_checkpoint.json').write_text('[]\n')
    mp.mp.dps=ar.dps; M=mp.mpf; tol=10**(-M(min(32,ar.dps-12))); start=time.time()
    cases=[('scalar','1.2','.4',[1]),('odd1','1.2','.4',[0,1]),
      ('even2-global','.7','1.1',[0,0,1]),('odd3','1.2','.4',[0,0,0,1]),
      ('mixed-global','.8','1.3',[1,-2,0,1]),('odd5','1.1','.35',[0,0,0,0,0,1])]
    for name,aa,bb,w in cases:
        if done('Gamma_second_defect',name) and done('spectral_jet_routes',f'{name}:r=4'): continue
        a,b=M(aa),M(bb)
        for r in range(1,5):
            lhs=defect_jet(r,a,b,w,terms)
            rhs=2**(r-1)*(linear_jet(r,a,1j*b,w)+linear_jet(r,a,-1j*b,w))-quadratic_jet(r,a,b,w,terms)
            compare('spectral_jet_routes',f'{name}:r={r}',lhs,rhs,tol)
        compare('Gamma_second_defect',name,defect_jet(2,a,b,w,terms),
                conjugate_chord(a,b,w,nodes)-local_second(w,b),tol)
    print('Spectral and Gamma routes:',len(records),flush=True)
    for name,aa,bb,w in cases[:3]:
        if done('cutoff_invariance',name): continue
        a,b=M(aa),M(bb);N=finite_head(a,b)
        compare('cutoff_invariance',name,defect_jet(3,a,b,w,terms,head=N),defect_jet(3,a,b,w,terms,head=N+3),tol)
    for aa,bb in [('1.2','.4'),('.6','1.2'),('1','.3'),('.5','.7')]:
        if done('ordinary_arctangent',aa+','+bb): continue
        a,b=M(aa),M(bb)
        compare('ordinary_arctangent',aa+','+bb,-4*arctan_square(a,b,terms),conjugate_chord(a,b,[1],nodes),tol)
    for aa,uu,vv in [('1.1','.2','.7'),('.7','-.1','.4'),('1.4','.3','-.2')]:
        if done('digamma_polarization',aa+','+uu+','+vv): continue
        a,u,v=map(M,(aa,uu,vv))
        ss=mp.nsum(lambda n:(mp.log(n+a+u)-mp.log(n+a+v))**2,[0,mp.inf])
        compare('ordinary_log_square',aa+','+uu+','+vv,gamma_chord(a,u,v,[1],nodes),ss,tol)
        rr=mp.nsum(lambda n:1/((n+a+u)*(n+a+v)),[0,mp.inf])
        compare('digamma_polarization',aa+','+uu+','+vv,rr,(mp.digamma(a+v)-mp.digamma(a+u))/(v-u),tol)
    for aa,bb in [('.3','.4'),('.5','.7'),('.7','.8')]:
        if done('reflected_polylogarithm',aa+','+bb): continue
        a,b=M(aa),M(bb)
        L1=lambda t:-mp.log(1-mp.exp(2j*mp.pi*a-2*mp.pi*b*t))
        rhs=2*mp.pi*b*mp.log(2)+2*mp.re(integral01(lambda t:(L1(t)-L1(1))/(1-t*t),nodes))
        compare('reflected_polylogarithm',aa+','+bb,arctan_square(a,b,terms)+arctan_square(1-a,b,terms),rhs,tol)
    b=M('.45')
    rhs=-mp.pi**2/8+mp.pi*b*mp.log(2)+mp.quad(lambda t:(-mp.log(-mp.expm1(-2*mp.pi*b*t))+
                mp.log(-mp.expm1(-2*mp.pi*b)))/(1-t*t),[0,M('.5'),1])
    compare('integer_polylog_endpoint','a=1',arctan_square(1,b,terms),rhs,tol)
    print('Ordinary sums and reflection:',len(records),flush=True)
    for aa,bb in [('.4','.3'),('.45','.8')]:
        a,b=M(aa),M(bb)
        for m in range(4):
            if done('negative_second_polylogs',f'm={m},a={aa},b={bb}'): continue
            w=[M(0)]*(2*m+1)
            for k in range(m+1):w[2*k]=mp.binomial(m,k)*b**(2*(m-k))
            rhs=quadratic_jet(2,a,b,w,terms)+quadratic_jet(2,1-a,b,w,terms)
            compare('negative_second_polylogs',f'm={m},a={aa},b={bb}',negative_second_bilateral(m,a,b,nodes),rhs,tol)
    a,b,c=map(M,['1.1','.35','.6'])
    weights=[[1],[0,0,1]]+([] if ar.quick else [[1,0,0,0,1]])
    for w in weights:
        if done('two_mass_spectral',str(w)) and done('mass_Gamma_covariance',str(w)): continue
        V=mass_chord(a,b,c,w,nodes)
        compare('mass_Gamma_covariance',str(w),V,covariance(a,b,c,w,nodes),tol)
        J=2*(quadratic_jet(2,a,b,w,terms)+quadratic_jet(2,a,c,w,terms))-two_mass_jet(2,a,b,c,w,terms)
        compare('two_mass_spectral',str(w),V,J,tol)
    compare('repeated_mass','W=1',two_mass_jet(2,a,b,b,[1],terms),4*quadratic_jet(2,a,b,[1],terms),tol)
    aa=M('.4')
    for w in ([1],[0,0,1]):
        if done('bilateral_mass_polylogs',str(w)): continue
        compare('bilateral_mass_polylogs',str(w),mass_chord(aa,b,c,w,nodes,bilateral=True),
                mass_chord(aa,b,c,w,nodes)+mass_chord(1-aa,b,c,w,nodes),tol)
    for w in ([1],[0,0,1],[1,0,0,0,1]):
        if done('confluent_covariance',str(w)) and done('finite_polygamma_resolvents',f'W={w},k=3'): continue
        h=M('.004')
        approx=mp.fsum(2*(-1)**k*mp.harmonic(k-1)/k*h**k*integer_series(k,a,b,w) for k in range(2,20))
        compare('confluent_covariance',str(w),mass_chord(a,b,mp.sqrt(b*b+h),w,nodes),approx,tol)
        for k in (1,2,3):
            compare('finite_polygamma_resolvents',f'W={w},k={k}',quadratic_value(k,a,b,w),integer_series(k,a,b,w),tol)
    print('Negative jets and covariances:',len(records),flush=True)
    for R in (1,2,3):
        for h in (0,1,3):
            if done('shift_primitives',f'R={R},h={h}'): continue
            a=M('1.2')
            compare('shift_primitives',f'R={R},h={h}',mp.diff(lambda x:hurwitz_primitive(R,h,x),a,R),mp.zeta(-h,a,derivative=1),tol)
    if not ar.quick:
        for r,w in [(2,[0,1]),(3,[1])]:
            if done('logarithmic_beta_jets',f'r={r},W={w}'): continue
            a,b=M('1.1'),M('.35')
            compare('logarithmic_beta_jets',f'r={r},W={w}',beta_defect(r,a,b,w),defect_jet(r,a,b,w,terms),tol)
            print('Beta integral:',r,w,flush=True)
    groups=dict(Counter(r['group'] for r in records))
    maximum=max(M(r['scaled_residual']) for r in records)
    data={'status':'PASS','comparisons':len(records),'dps':ar.dps,'threshold':mp.nstr(tol,8),
      'terms':terms,'Gauss_nodes':nodes,'maximum_scaled_residual':mp.nstr(maximum,12),'groups':groups,
      'python_version':platform.python_version(),'mpmath_version':mp.__version__,'elapsed_seconds_this_invocation':round(time.time()-start,3),
      'quick':ar.quick,'resumed':ar.resume,'meaning':'Floating-point diagnostics only; no interval or validated-tail certificates.','records':records}
    name='numeric_quick_results.json' if ar.quick else 'numeric_results.json'
    (ROOT/'results'/name).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='records'},indent=2),flush=True)
if __name__=='__main__':main()
