from __future__ import annotations
import argparse,json,platform
from pathlib import Path
import mpmath as mp
import sympy as sp
import mellin_numeric as num
import mellin_exact as exact


def evaluate(expr):
    return sp.lambdify((),expr,modules=[{'Z':lambda a,b:num.double(int(a),int(b))},'mpmath'])()

def run(output:Path):
    mp.mp.dps=45
    records=[]
    def check(name,lhs,rhs,tolerance='1e-33'):
        error=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
        if error>=mp.mpf(tolerance):
            raise AssertionError(f'{name}: scaled error {mp.nstr(error,12)}')
        records.append({'name':name,'working_decimal_digits':mp.mp.dps,'lhs':mp.nstr(lhs,43),
          'rhs':mp.nstr(rhs,43),'scaled_error':mp.nstr(error,8),'tolerance':tolerance})
        print(name,mp.nstr(error,5),flush=True)
    for m,n,a in [(1,1,'.3'),(2,1,'-.5'),(2,2,'.4'),(3,1,'-1.4'),(3,2,'.2'),(4,1,'-.2'),(3,3,'.5'),(2,4,'-1.2'),(1,5,'.35')]:
        a=mp.mpf(a);check(f'master_{m}_{n}_{a}',num.direct(a,m,n),num.master(a,m,n))
    for m,n,h in [(1,1,0),(2,1,0),(3,1,0),(2,2,0),(3,2,0),(3,3,0),(2,2,1),(3,1,2),(1,1,3),(2,1,4),(2,3,2),(1,4,1)]:
        check(f'jet_{m}_{n}_{h}',num.direct(0,m,n,h=h),num.resonant_jet(m,n,h))
    for m,n,h in [(1,1,0),(2,1,0),(1,3,1),(2,2,2),(3,2,1)]:
        check(f'negative_jet_{m}_{n}_{h}',num.direct(-1,m,n,h=h),evaluate(exact.jet(m,n,h,True)))
    for N,a,m,n,h in [(2,1,1,1,0),(3,1,2,1,0),(3,2,2,2,0),(2,0,2,1,0),(2,1,2,2,1),(5,-1,3,2,0),(5,3,2,3,2),(4,0,1,4,1),(6,5,3,1,0),(4,2,3,3,0)]:
        check(f'recurrence_{N}_{a}_{m}_{n}_{h}',num.direct(a,m,n,N,h),evaluate(exact.moment(N,a,m,n,h)))
    for m,n,h in [(1,2,0),(1,1,1),(2,3,0),(2,2,1),(1,4,0),(3,4,0),(1,2,2)]:
        check(f'central_{m}_{n}_{h}',num.direct(mp.mpf('.5'),m,n,h=h),evaluate(exact.central(m,n,h)))
    for z in ['.25','.7','1','2','5']:
        z=mp.mpf(z);r=1-1/z
        rhs=mp.mpf(2) if z==1 else (mp.log(z)+mp.polylog(2,r))/r
        check(f'multiscale_{z}',num.direct(1,1,1,N=2,w=z),rhs)
    for A,B,q in [(1,1,'.3'),(1,3,'1.2'),(3,1,'2.1'),(2,4,'.7'),(4,2,'1.5')]:
        q=mp.mpf(q)
        check(f'connected_shift_{A}_{B}_{q}',num.connected(A,B,q+1)-num.connected(A,B,q),-q**(-A)*num.delta(B,q))
        check(f'connected_stuffle_{A}_{B}_{q}',num.connected(A,B,q)+num.connected(B,A,q),num.delta(A,q)*num.delta(B,q)+num.delta(A+B,q))
    for A,B,q in [(2,1,'.3'),(2,2,'1'),(4,3,'1.7'),(7,1,'2.2')]:
        q=mp.mpf(q)
        check(f'tail_refinement_{A}_{B}_{q}',num.double(A,B,q,64,24),num.double(A,B,q,96,32))
    for d,h in [(0,0),(0,3),(1,2),(3,3),(5,4)]:
        lhs=mp.quad(lambda x:x**d*mp.log(x/(1-x))**h,[0,.5,1])
        check(f'beta_moment_{d}_{h}',lhs,evaluate(exact.beta_moment(d,h)))
    record={'status':'PASS','python':platform.python_version(),'mpmath':mp.__version__,
      'number_of_checks':len(records),'maximum_scaled_error':mp.nstr(max(mp.mpf(r['scaled_error']) for r in records),10),
      'scope':'High-precision diagnostics; no interval certificates and no inference of equality from residuals.',
      'double_zeta_method':'finite sums plus Euler--Maclaurin tails, M=64,K=24; independent refinement M=96,K=32',
      'records':records}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(record,indent=2)+'\n')
    print('PASS:',len(records),'checks; maximum scaled error',record['maximum_scaled_error'])

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data/numerical_results.json');run(p.parse_args().output)
