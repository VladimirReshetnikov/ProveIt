"""Optional exact large-n diagnostics, not a proof or certified error bound."""
import sys
sys.dont_write_bytecode=True
import argparse,json
import mpmath as mp
from exact import exact_selected
from formulas import constants,inverse_centers

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-n',type=int,default=100)
    args=p.parse_args()
    if args.max_n<1:p.error('--max-n must be positive')
    mp.mp.dps=80
    L,beta,C,c1,c2=constants()
    selected=sorted({args.max_n}|{i for i in [25,50,100,200,400,800,3200] if i<=args.max_n})
    values=exact_selected(args.max_n,selected)
    result=[]
    for n in selected:
        z=mp.mpf(n);a=values[n]
        loglead=2*mp.loggamma(z+1)-2*z*mp.log(L)-mp.mpf(5)/4*mp.log(z)+beta*mp.sqrt(z)+mp.log(C)
        ratio=mp.exp(mp.log(a)-loglead)
        x,h,X1,X2=inverse_centers(mp.log(a))
        data=dict(n=n,ratio=ratio,sqrt_n_times_leading_error=mp.sqrt(z)*(ratio-1),n_times_first_corrected_error=z*(ratio-1-c1/mp.sqrt(z)),inverse_center_error=X1-z,inverse_refined_center_error=X2-z)
        result.append({k:v if isinstance(v,int) else mp.nstr(v,35) for k,v in data.items()})
    print(json.dumps({'diagnostic_only':True,'checks':result},indent=2))
if __name__=='__main__':main()
