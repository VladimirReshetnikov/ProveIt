#!/usr/bin/env python3
"""Scientific diagnostic plot; no floating-point result is a proof certificate.

Dependencies: numpy, scipy, matplotlib. All numerical points and analytic
spectral-tail majorants are retained. Rounding is not enclosed.
"""
from pathlib import Path
from math import factorial, log, exp, sqrt
import csv
import json
import numpy as np
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter

ROOT=Path(__file__).resolve().parents[2]
RESULTS=ROOT/'results'/'lerch'
FIGURES=ROOT/'figures'
R2=1.29982837988436943384723341025066892915
R3=1.77628448580819385266276143262737862711


def tail_majorant(k,rho,M):
    """Bound the omitted function value, evaluated here in floating point.

    Beyond M, the positive summands are bounded by
    k! rho^M (H_k+log(x))^2 / x^(k+1). The decreasing majorant's
    sum is at most its first term plus its integral to infinity.
    """
    H=sum(1/j for j in range(1,k+1));L=log(M)+H
    integral=M**(-k)*(L*L/k+2*L/(k*k)+2/(k*k*k))
    return factorial(k)*rho**M*(L*L/M**(k+1)+integral)


def point(k,rho):
    H=sum(1/j for j in range(1,k+1));V=sum(1/j**2 for j in range(1,k+1))
    if rho==0:
        return exp(H-sqrt(V)),0,0,'exact elementary formula, evaluated in double precision'
    if rho==1:
        return (R2 if k==2 else R3),0,0,'endpoint diagnostic from 60-digit Hurwitz evaluation; root bracket separately certified'
    M=262144 if k==2 else 4096
    m=np.arange(M,dtype=float)
    weights=np.exp(m*np.log(rho))*factorial(k)
    def F(a):
        x=a+m;y=H-np.log(x)
        return np.dot(weights,(y*y-V)/x**(k+1))
    bracket=(1.2997,1.3001) if k==2 else (1.75,1.96)
    a=brentq(F,*bracket,xtol=5e-15)
    return a,M,tail_majorant(k,rho,M),'floating-point spectral solve; function-tail majorant only, rounding not enclosed'


def main():
    RESULTS.mkdir(parents=True,exist_ok=True);FIGURES.mkdir(parents=True,exist_ok=True)
    minimum=json.loads((RESULTS/'minimum_diagnostic.json').read_text())
    rmin=float(minimum['rho_min']);amin=float(minimum['a_min'])
    grids={2:sorted(set(np.linspace(.9995,1,37).tolist()+[rmin])),
           3:np.linspace(0,1,41).tolist()}
    rows=[]
    for k in (2,3):
        for rho in grids[k]:
            a,M,tail,status=point(k,rho)
            rows.append({'k':k,'rho':format(rho,'.17g'),'a_lower':format(a,'.17g'),
                         'spectral_terms':M,'function_tail_majorant':format(tail,'.17g'),
                         'status':status})
        print('Diagnostic points complete for k=',k,flush=True)
    with (RESULTS/'shape_plot_points.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)

    plt.rcParams.update({'font.size':10,'axes.titlesize':11,'axes.labelsize':10,
                         'font.family':'DejaVu Sans','pdf.fonttype':42,
                         'axes.spines.top':False,'axes.spines.right':False})
    fig,axs=plt.subplots(1,2,figsize=(10.1,3.65),layout='constrained')
    for ax,k in zip(axs,(2,3)):
        data=[r for r in rows if r['k']==k]
        x=np.array([float(r['rho']) for r in data]);y=np.array([float(r['a_lower']) for r in data])
        if k==2:
            y=(y-R2)*1e6
            ax.plot(x,y,color='#165a7b',lw=1.8)
            ax.scatter([rmin],[(amin-R2)*1e6],color='#ac3d36',s=25,zorder=4)
            ax.annotate('unique minimum',xy=(rmin,(amin-R2)*1e6),
                        xytext=(.99971,-.45),arrowprops={'arrowstyle':'->','color':'#555555'},
                        fontsize=9,color='#333333')
            ax.set(title='Second order: the final upturn',
                   xlabel=r'$\rho$',ylabel=r'$10^6\,[a_2(\rho)-a_2(1)]$')
            ax.xaxis.set_major_formatter(FormatStrFormatter('%.4f'))
            ax.set_xticks([.9995,.9996,.9997,.9998,.9999,1])
            ax.tick_params(axis='x',labelrotation=25)
            ax.axhline(0,color='#b8b8b8',lw=.7,zorder=0)
        else:
            ax.plot(x,y,color='#165a7b',lw=1.8)
            ax.set(title='Third order: strict decrease',xlabel=r'$\rho$',ylabel=r'$a_3(\rho)$')
        ax.grid(alpha=.18)
    fig.savefig(FIGURES/'lerch_shape_diagnostic.pdf')
    fig.savefig(FIGURES/'lerch_shape_diagnostic.png',dpi=180)
    plt.close(fig)
    metadata={'status':'diagnostic floating-point plot; global shapes proved analytically using exact endpoint certificates',
              'source':'code/lerch/plot_diagnostic.py','points':len(rows),
              'function_tail_majorant_max':max(float(r['function_tail_majorant']) for r in rows),
              'tail_bound_scope':'majorant for omitted function values only, not an interval rounding or root-error certificate',
              'minimum_marker_source':'results/lerch/minimum_diagnostic.json',
              'csv':'results/lerch/shape_plot_points.csv',
              'figures':['figures/lerch_shape_diagnostic.pdf','figures/lerch_shape_diagnostic.png']}
    (RESULTS/'shape_plot_metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2),flush=True)


if __name__=='__main__':
    main()
