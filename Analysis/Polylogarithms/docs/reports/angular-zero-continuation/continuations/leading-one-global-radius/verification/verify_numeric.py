#!/usr/bin/env python3
"""Floating-point diagnostics and figure generation; NOT interval certificates."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import numpy as np
import scipy
import mpmath as mp
from scipy.special import spence
from scipy.optimize import brentq
from core_numeric import LeadingOne


def direct_series(b:float,z:complex,terms:int=1024)->mp.mpc:
    bb=mp.mpf(str(b)); zz=mp.mpc(z)
    h=mp.mpf(0);power=zz;total=mp.mpc(0)
    for n in range(2,terms+1):
        h+=mp.power(n-1,-bb)
        power*=zz
        total+=h*power/n
    return total


def q2(u:np.ndarray)->np.ndarray:
    ans=np.zeros_like(u,dtype=float)
    ok=(u>0)&(u<1)
    v=u[ok];T=-np.log(v)
    ans[ok]=v*T*T/2+(1-v)*(spence(1-v)-T*np.log1p(-v))
    return ans


def main()->None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--figures-dir',type=Path)
    args=ap.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
    path=args.output_dir/'numeric-results.json'
    if path.exists():raise FileExistsError(path)
    mp.mp.dps=70
    bs=[.25,.5,1.,2.,4.,8.]
    models={b:LeadingOne(b,256) for b in bs}
    zs=[.2+.3j,.5+.4j,-.75+0j,.25+0j]
    cross=[]
    for b in bs:
        lower=LeadingOne(b,128)
        for z in zs:
            ref=direct_series(b,z)
            high=models[b].value(z)
            low=lower.value(z)
            err=float(abs(mp.mpc(high)-ref))
            assert err<2e-10,(b,z,err)
            cross.append({'b':b,'z':[z.real,z.imag],
              'abs_error_against_70_digit_series':err,
              '128_vs_256_difference':abs(high-low)})
    radii=np.linspace(0,1,101)
    curves=[]
    for b in bs:
        vals=np.array([models[b].eta(float(r)) for r in radii])
        diff=np.diff(vals)
        if b<1:assert np.all(diff>0),(b,diff.min())
        if b>1:assert np.all(diff<0),(b,diff.max())
        if b==1:assert np.max(np.abs(vals-.5))<2e-10
        curves.append({'b':b,'rho':radii.tolist(),'eta':vals.tolist(),
                       'maximum_grid_increment':float(diff.max()),
                       'minimum_grid_increment':float(diff.min())})
    table=[]
    for b in bs:
        table.append({'b':b,'eta':[models[b].eta(r) for r in (0,.25,.5,.75,1)]})
    x=models[2.].eta(.5)
    zero=brentq(lambda v:float(q2(np.array([x+v]))[0]-q2(np.array([x-v]))[0]),
                 .0001,x)
    data={'status':'PASS','evidence_class':'floating-point diagnostics, not interval certificates',
      'versions':{'numpy':np.__version__,'scipy':scipy.__version__,'mpmath':mp.__version__},
      'quadrature_order':256,'comparison_series_terms':1024,'series_dps':70,
      'cross_checks':cross,'max_abs_crosscheck_error':max(r['abs_error_against_70_digit_series'] for r in cross),
      'table_radii':[0,.25,.5,.75,1],'table':table,'curves':curves,
      'reflected_example':{'b':2,'rho':.5,'x':x,'positive_crossing_v':zero}}
    path.write_text(json.dumps(data,indent=2)+'\n')
    if args.figures_dir:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        args.figures_dir.mkdir(parents=True,exist_ok=True)
        fig,ax=plt.subplots(figsize=(7.2,4.25))
        for row in curves:
            ax.plot(row['rho'],row['eta'],label=f"b = {row['b']:g}",linewidth=1.7)
        ax.set_xlabel(r'Radius $\rho$')
        ax.set_ylabel(r'Normalized zero coordinate $\eta_{1,b}(\rho)$')
        ax.set_xlim(0,1);ax.legend(ncol=3,loc='best',fontsize=9)
        ax.grid(True,alpha=.25);fig.tight_layout()
        fig.savefig(args.figures_dir/'radial_motion.pdf')
        fig.savefig(args.figures_dir/'radial_motion.png',dpi=180)
        plt.close(fig)
        v=np.linspace(0,1-x,600)
        delta=q2(x+v)-q2(x-v)
        fig,ax=plt.subplots(figsize=(7.2,4.0))
        ax.plot(v,delta,linewidth=1.8)
        ax.axhline(0,linewidth=.8,linestyle='--')
        ax.axvline(zero,linewidth=.8,linestyle=':')
        ax.set_xlabel(r'Reflection displacement $v$')
        ax.set_ylabel(r'$Q_2(x+v)-Q_2(x-v)$')
        ax.set_title(r'$x=\eta_{1,2}(1/2)$: one negative-to-positive crossing',fontsize=11)
        ax.grid(True,alpha=.25);fig.tight_layout()
        fig.savefig(args.figures_dir/'reflected_difference.pdf')
        fig.savefig(args.figures_dir/'reflected_difference.png',dpi=180)
        plt.close(fig)
    print(json.dumps({'status':'PASS','cross_checks':len(cross),
          'max_error':data['max_abs_crosscheck_error'],
          'root_grid_points':len(bs)*len(radii),'table':table},indent=2))
if __name__=='__main__':main()
