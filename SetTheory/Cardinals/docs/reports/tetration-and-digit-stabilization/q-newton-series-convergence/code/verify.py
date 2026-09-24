"""Reproduce exact checks and the article's numerical tables.
Run from any directory: python code/verify.py
"""
from pathlib import Path
from fractions import Fraction as Q
import csv, json, platform, sys
import mpmath
from mpmath import mp
from tetration import TetrationModel, original_qnewton_partial

OUT=Path(__file__).resolve().parents[1]/'data'
OUT.mkdir(exist_ok=True)
checks=[]

def check(name, cond, value=None):
    if not cond:
        raise AssertionError(f'{name}: {value}')
    checks.append({'name':name,'passed':True,'value':str(value) if value is not None else None})


def qb(n,k,q):
    if k<0 or k>n: return Q(0)
    r=Q(1)
    for j in range(1,k+1): r*= (1-q**(n-k+j))/(1-q**j)
    return r

# Exact rational verification on monomial data of the q-Newton identity.
exact_count=0
for q in (Q(1,2),Q(2,3),Q(3,4)):
    for n in range(1,9):
        for m in range(0,13):
            beta=sum(((-1)**(n-k)*q**((n-k)*(n-k-1)//2)*qb(n,k,q)*q**(m*k)
                      for k in range(n+1)),Q(0))
            rhs=Q(1)
            for j in range(n): rhs*=q**m-q**j
            assert beta==rhs,(q,n,m)
            exact_count+=1
check('Exact rational monomial q-Newton identities',exact_count==312,exact_count)

mp.dps=110
rows=[]; bdrows=[]; coefrows=[]; samples=[]
for label,q in [('half',mp.mpf('0.5')),('sqrt2',mp.log(2)),('nine_tenths',mp.mpf('0.9'))]:
    model=TetrationModel.build(q,terms=700,digits=95)
    ahat=model.scaled_newton_coefficients(256)
    check(f'{label}: all 700 spectral coefficients positive', all(x>0 for x in model.b[1:]))
    check(f'{label}: all 256 Newton coefficients negative',all(x<0 for x in ahat[1:]))
    check(f'{label}: R enclosure ordered',model.R_lower<=model.R<=model.R_upper)
    for z in [mp.mpf('0'),mp.mpf('0.5'),mp.mpf('2.25'),mp.mpc('0.3','0.7')]:
        lhs=model.evaluate(z+1)
        rhs=mp.exp(q/model.L*model.evaluate(z))
        err=abs(lhs-rhs)
        check(f'{label}: functional equation at {z}',err<mp.mpf('1e-60'),mp.nstr(err,8))
    for j in range(1,9):
        val=(-1)**(j-1)*mp.re(model.derivative(mp.mpf('0.5'),j))
        check(f'{label}: derivative sign order {j}',val>0,mp.nstr(val,8))
    z=mp.mpf('0.5'); truth=model.evaluate(z)
    partials=model.newton_partial_sums(z,ahat)
    for n in [4,8,16,32,64,128]:
        err=abs(partials[n]-truth)
        rows.append([label,mp.nstr(q,30),n,mp.nstr(mp.re(truth),50),mp.nstr(err,16)])
    K=1/mp.log(model.a)
    pp=mp.qp(q*q,q)
    for n in [16,32,64,128,256]:
        coefrows.append([label,n,mp.nstr(q*n*model.b[n],18),
                        mp.nstr(-n*ahat[n]*pp/K,18)])
    bp=model.newton_partial_sums(-2,ahat)
    # A non-singular boundary point with q^(z+2)=-1.
    zp=mp.mpc(-2,mp.pi/mp.log(q))
    bm=model.newton_partial_sums(zp,ahat)
    for n in [16,32,64,128,256]:
        bdrows.append([label,n,mp.nstr(mp.re(bp[n]),18),
                       mp.nstr(mp.re(bp[n])+K*mp.log(n),18),
                       mp.nstr(mp.re(bm[n]),18)])
    samples.append({'label':label,'q':mp.nstr(q,65),'a':mp.nstr(model.a,65),
                    'R':mp.nstr(model.R,65),'T_half':mp.nstr(mp.re(truth),65),
                    'koenigs_steps':model.koenigs_steps,
                    'relative_R_enclosure':mp.nstr((model.R_upper-model.R_lower)/model.R,8)})
    # The literal alternating formula is recomputed at much higher precision.
    for n in [4,8,16,24]:
        with mp.workdps(420):
            qhi=mp.log(2) if label=='sqrt2' else mp.mpf('0.5' if label=='half' else '0.9')
            direct=original_qnewton_partial(qhi,mp.mpf('0.5'),n)
        err=abs(direct-partials[n])
        check(f'{label}: original double sum N={n}',err<mp.mpf('1e-60'),mp.nstr(err,8))
    print(label,'T(1/2)=',mp.nstr(truth,35),'checks passed',flush=True)

for filename,header,data in [
 ('convergence.csv',['case','q','N','T_half','absolute_error'],rows),
 ('boundary.csv',['case','N','P_N_at_minus2','renormalized_P_N','P_N_at_boundary_phase_pi'],bdrows),
 ('coefficient_asymptotics.csv',['case','n','q_n_b_n','normalized_Newton_coefficient'],coefrows)]:
    with (OUT/filename).open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(header);writer.writerows(data)
(OUT/'samples.json').write_text(json.dumps(samples,indent=2)+'\n')
(OUT/'verification.json').write_text(json.dumps({'python':sys.version,'platform':platform.platform(),
    'mpmath':mpmath.__version__,'working_dps':110,'spectral_terms':700,
    'exact_rational_identity_count':exact_count,'check_count':len(checks),'checks':checks},indent=2)+'\n')
print(f'{len(checks)} checks passed, including {exact_count} exact rational identities.')
