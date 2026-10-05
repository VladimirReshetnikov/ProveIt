#!/usr/bin/env python3
"""High-precision diagnostics against exact coefficients; none are proofs.
Run after verify_exact.py. Formula data are from symbolic_results.json,
derived independently by the symbolic saddle and inverse calculation. No fits are used.
"""
import argparse,json,pathlib,sys
import mpmath as mp
import sympy as s

HERE=pathlib.Path(__file__).resolve().parent
def require(test,msg):
    if not test: raise RuntimeError(msg)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--max-n',type=int,default=2000)
    p.add_argument('--formulas',default=str(HERE/'symbolic_results.json'))
    p.add_argument('--output',default='diagnostics.json')
    args=p.parse_args()
    mp.mp.dps=100
    a=list(map(int,json.loads((HERE/f'exact_coefficients_{args.max_n}.json').read_text())))
    form=json.loads(pathlib.Path(args.formulas).read_text())
    K=13*mp.pi**2/24; delta=13*mp.sqrt(2)/768; A=delta*(2*mp.sqrt(K))**3
    def ev(p,**kw):
        symbols={k:s.Symbol(k) for k in kw}
        expr=s.sympify(p,locals=symbols)
        f=s.lambdify(list(symbols.values()),expr,'mpmath')
        return f(*kw.values())
    bs=[ev(p,K=K) for p in form['b_in_K']]
    ls=[mp.mpf(0)]+[ev(p,K=K) for p in form['lambda_in_K']]
    # Independent recomputation of b_r via exact half-integer Bessel polynomial.
    ds=[ev(p) for p in form['d']]
    for r,b in enumerate(bs):
        direct=sum(ds[j]*(2*K)**j*(-1)**(r-j)*mp.factorial(r+2)/
          (mp.factorial(r-j)*mp.factorial(2*j+2-r)*2**(r-j))
          for j in range(max(0,(r-1)//2),r+1))
        require(mp.almosteq(b,direct),'independent b recomputation differs')
    vals=[]
    for n in [100,200,500,1000,1500,1936,2000,4000,8000,16000]:
        if n>args.max_n: continue
        z=2*mp.sqrt(K*n); y=mp.mpf(a[n]); Y=mp.log(y); T=3*mp.log(Y)-mp.log(A)
        lead=delta*mp.exp(z)/mp.mpf(n)**mp.mpf('1.5')
        ratio=y/lead
        partial=mp.mpf(0); corrections=[]
        for r,b in enumerate(bs):
            partial+=b/z**r
            corrections.append({'order':r,'ratio_to_truncation':str(y/(lead*partial)),
              'relative_error_prediction':str((lead*partial-y)/y),
              'scaled_remainder_in_ratio':str((ratio-partial)*z**(r+1)),
              'next_b':str(bs[r+1]) if r+1<len(bs) else None})
        z0=-3*mp.lambertw(-(A/y)**(mp.mpf(1)/3)/3,-1)
        require(abs(mp.im(z0))<mp.mpf('1e-90'),'Lambert branch is complex')
        z0=mp.re(z0)
        inverse=[]
        zcorr=z0
        inverse.append({'method':'Lambert leading','estimated_n':str(z0*z0/(4*K)),
          'n_minus_estimate':str(n-z0*z0/(4*K))})
        params={f'l{i}':ls[i] for i in range(1,5)}
        for r in range(1,5):
            zcorr+=ev(form['Q_lambert_z'][str(r)],**params)/z0**r
            inverse.append({'method':f'Lambert corrected order {r}',
              'estimated_n':str(zcorr*zcorr/(4*K)),
              'n_minus_estimate':str(n-zcorr*zcorr/(4*K))})
        nsum=mp.mpf(0)
        for r in range(-2,4):
            nsum+=ev(form['N_inverse_n'][str(r)],T=T,**params)/Y**r
            inverse.append({'method':f'log inverse through Y^{(-r)}',
              'estimated_n':str(nsum/(4*K)),
              'n_minus_estimate':str(n-nsum/(4*K))})
        vals.append({'n':n,'z':str(z),'ratio_to_leading':str(ratio),
          'z_times_leading_ratio_minus_1':str(z*(ratio-1)),
          'coefficient_corrections':corrections,'inverse':inverse})
    output={'precision_decimal_digits':mp.mp.dps,'python_optimization':sys.flags.optimize,
      'warning':'Finite numerical diagnostics support/check formulas; they do not prove asymptotics.',
      'max_n':args.max_n,'K':str(K),'delta':str(delta),'A':str(A),
      'b':list(map(str,bs)),'lambda':list(map(str,ls[1:])),
      'lambert_leading_index_bias_limit':str(3/(2*K)+mp.mpf(1)/6),
      'diagnostics':vals}
    (HERE/args.output).write_text(json.dumps(output,indent=2)+'\n')
    print('n; leading ratio; relative errors orders 1,2,4,8; Lambert n-bias; corrected order4 bias; logarithmic through Y^-3 bias')
    for row in vals:
        c=row['coefficient_corrections'];inv=row['inverse']
        print(row['n'],mp.nstr(mp.mpf(row['ratio_to_leading']),14),
          *(mp.nstr(mp.mpf(c[r]['relative_error_prediction']),10) for r in [1,2,4,8]),
          mp.nstr(mp.mpf(inv[0]['n_minus_estimate']),14),
          mp.nstr(mp.mpf(inv[4]['n_minus_estimate']),10),
          mp.nstr(mp.mpf(inv[-1]['n_minus_estimate']),10))
    print('Predicted Lambert bias limit:',output['lambert_leading_index_bias_limit'])

if __name__=='__main__':main()
