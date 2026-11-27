"""Plot exact small-field data and finite bounds (not Monte Carlo).

The bounds for n=200 use exact Fraction arithmetic and elementary rational
majorants for the exponential and infinite products. Only plotting needs
matplotlib. Run from any directory; outputs go to ../data and ../figures.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parents[1]


def odd_product(q, n):
    out = F(1)
    for j in range(3, n, 2):
        out *= 1 - F(1, q**j)
    return out


def product_lower_bounds(q, truncation=80):
    gamma = F(1)
    for j in range(1, truncation + 1):
        gamma *= 1 - F(1, q**j)
    gamma *= 1 - F(1, (q-1) * q**truncation)
    c = odd_product(q, 2*truncation)
    tail = F(1, q**(2*truncation+1)) / (1-F(1, q*q))
    c *= 1-tail
    assert gamma > 0 and c > 0
    return gamma, c


def finite_bounds(q, n, offset):
    D = n*(n-1)//2
    d = D-1
    t = d+offset
    R = n//5
    b = (n-R)*(n-R-1)//2
    rho = F(2*q-1, q*q)
    K = 4*q*(q-1)
    gamma_lo, c_lo = product_lower_bounds(q)
    cn = odd_product(q, n)
    x = F(K*t, q**R)
    tail = F(t, q**(n-2))
    assert 0 <= x < 1 and 0 <= tail < 1
    # exp(x) <= 1/(1-x); p >= q^-1(1-q^-(n-2));
    # (1-q^-(n-2))^t >= 1-t*q^-(n-2).
    exp_up = 1/(1-x)
    diag_up = F(q)**offset / (cn*(1-tail))
    near_chi_up = F(q)/(gamma_lo*c_lo) * F(q)**(-b) * (q*rho)**t/(1-tail)
    chi_up = exp_up-1 + diag_up + near_chi_up
    # p <= q^-1, so these bounds avoid enormous p^t fractions.
    null_false_positive_up = cn*F(q)**(-offset)
    recovery_failure_up = (
        F(q)**(-offset)/(q-1)*exp_up
        + F(q)**(D-b)*rho**t/((q-1)*gamma_lo)
    )
    return {
        'q':q,'n':n,'D':D,'d':d,'t':t,'offset':offset,'R':R,
        'chi_up':chi_up,'bayes_up':diag_up,
        'null_fp_up':null_false_positive_up,
        'linear_failure_up':recovery_failure_up,
    }


def main():
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    data=json.loads((ROOT/'data/independent_hidden_forms.json').read_text())
    records=data[0]['exact_span_process']['records']
    bounds=[finite_bounds(2,200,c) for c in range(-12,13)]
    low=next(x for x in bounds if x['offset']==-10)
    high=next(x for x in bounds if x['offset']==10)
    # Rational comparisons certify the stated rounded illustrations.
    assert low['chi_up'] < 4*F(171,10000)**2  # TV < 0.0171
    assert low['bayes_up'] < F(1165,1000000)
    assert high['null_fp_up'] < F(82,100000)
    assert high['linear_failure_up'] < F(977,1000000)
    serial=[]
    for r in bounds:
        s={k:v for k,v in r.items() if not isinstance(v,F)}
        for k,v in r.items():
            if isinstance(v,F):s[k+'_decimal']=float(v)
        s['tv_upper_decimal']=min(1,math.sqrt(float(r['chi_up']))/2)
        s['tv_lower_decimal']=max(0,1-float(r['null_fp_up']))
        s['linear_recovery_lower_decimal']=max(0,1-float(r['linear_failure_up']))
        serial.append(s)
    result={'arithmetic':'exact Fraction; plotted decimals are rounded',
      'rational_majorants':'exp(x)<=1/(1-x), Bernoulli inequality, product-tail sum bound',
      'certified_n200_binary_examples':{
        'd':19899,'t_below':19889,'TV_below_lt':'0.0171','optimal_recovery_below_lt':'0.001165',
        't_above':19909,'null_false_positive_lt':'0.00082','linear_recovery_failure_lt':'0.000977'},
      'bounds':serial}
    (ROOT/'data/finite_bound_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
      'axes.spines.top':False,'axes.spines.right':False,
      'axes.labelcolor':'#213547','text.color':'#213547'})
    fig,axs=plt.subplots(1,2,figsize=(10.8,4.0),layout='constrained')
    ax=axs[0]
    xs=[r['t'] for r in records]
    ax.plot(xs,[r['tv_decimal'] for r in records],color='#007d8a',lw=2.1,label='Total variation (exact)')
    ax.plot(xs,[r['gaussian_recovery_decimal'] for r in records],color='#c36a30',lw=2.1,label='Linear recovery (exact)')
    ax.axvline(5,color='#8b98a5',ls=':',lw=1.1)
    ax.set(xlim=(0,16),ylim=(-.025,1.025),xlabel='Number of observations',ylabel='Probability / distance',title='Exact experiment: q = 2, n = 4')
    ax.grid(axis='y',alpha=.18);ax.legend(loc='lower right',frameon=False,fontsize=8.5)
    ax=axs[1];xs=[r['offset'] for r in serial]
    ax.plot(xs,[r['tv_upper_decimal'] for r in serial],color='#007d8a',lw=2.0,label='TV upper bound')
    ax.plot(xs,[r['tv_lower_decimal'] for r in serial],color='#007d8a',lw=1.8,ls='--',label='TV lower bound')
    ax.plot(xs,[r['linear_recovery_lower_decimal'] for r in serial],color='#c36a30',lw=1.8,label='Recovery lower bound')
    ax.axvline(0,color='#8b98a5',ls=':',lw=1.1)
    ax.set(xlim=(-12,12),ylim=(-.025,1.025),xlabel='Observations minus d = 19,899',title='Proved finite bounds: q = 2, n = 200')
    ax.grid(axis='y',alpha=.18);ax.legend(loc='upper left',frameon=False,fontsize=8.5)
    (ROOT/'figures').mkdir(exist_ok=True)
    fig.savefig(ROOT/'figures/hidden_form_transition.pdf',bbox_inches='tight')
    fig.savefig(ROOT/'figures/hidden_form_transition.png',dpi=180,bbox_inches='tight')
    print(json.dumps(result['certified_n200_binary_examples'],indent=2))


if __name__=='__main__':
    main()
