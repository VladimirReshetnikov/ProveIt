#!/usr/bin/env python3
"""Finite exact-input Lambert-rounding diagnostics, not an eventual proof."""
import argparse,json,pathlib,sys
import mpmath as mp

HERE=pathlib.Path(__file__).resolve().parent
def main():
    p=argparse.ArgumentParser()
    p.add_argument('--max-n',type=int,default=8000)
    p.add_argument('--output',default='lambert_rounding_scan.json')
    args=p.parse_args()
    a=list(map(int,json.loads((HERE/f'exact_coefficients_{args.max_n}.json').read_text())))
    mp.mp.dps=70
    K=13*mp.pi**2/24; C=13*mp.sqrt(2)/768; A=C*(2*mp.sqrt(K))**3
    failures=[]; nonreal=[]; transitions=[]; prev_bad=None; bias_min=None; bias_max=None
    for n in range(1,len(a)):
        y=mp.mpf(a[n]); z0=-3*mp.lambertw(-(A/y)**(mp.mpf(1)/3)/3,-1)
        if abs(mp.im(z0))>mp.mpf('1e-60'):
            nonreal.append(n);continue
        z0=mp.re(z0); n0=z0*z0/(4*K); bias=mp.mpf(n)-n0
        if bias_min is None or bias<bias_min[1]:bias_min=(n,bias)
        if bias_max is None or bias>bias_max[1]:bias_max=(n,bias)
        bad=int(mp.floor(n0+mp.mpf('.5')))!=n
        if bad:failures.append(n)
        if bad!=prev_bad:
            transitions.append({'n':n,'rounding_correct':not bad,'bias':str(bias)})
        prev_bad=bad
    last_failure=max(failures+nonreal,default=0)
    result={'max_n':args.max_n,'precision_decimal_digits':mp.mp.dps,
      'python_optimization':sys.flags.optimize,
      'warning':'Observed finite range only; does not prove eventual exact recovery.',
      'nonreal_indices':nonreal,'failed_rounding_indices':failures,
      'verified_rounding_range':[last_failure+1,args.max_n],
      'transitions':transitions,
      'bias_min':{'n':bias_min[0],'value':str(bias_min[1])},
      'bias_max':{'n':bias_max[0],'value':str(bias_max[1])}}
    (HERE/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='failed_rounding_indices'},indent=2))
if __name__=='__main__':main()
