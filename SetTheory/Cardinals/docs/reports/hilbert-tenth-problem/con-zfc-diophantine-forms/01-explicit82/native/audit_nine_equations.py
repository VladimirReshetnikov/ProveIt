"""Finite all-value checks of the displayed nine residuals against the JSON DAG."""
from pathlib import Path
import json,random
ROOT=Path(__file__).resolve().parent
p=json.loads((ROOT/'k215_native72_system.json').read_text())
random.seed(7209)
for case in range(64):
    v={n:random.randint(-2,5) for n in p['positive_witnesses']+p['fixed_numerals']}
    env=dict(v)
    for n,op,l,r in p['source']:
        l=env[l] if isinstance(l,str) else l;r=env[r] if isinstance(r,str) else r
        env[n]=l+r if op=='+' else l-r if op=='-' else l*r
    q=v['Bm1']*v['Jrep']+1;X=v['w']*q**3;Y=v['s']*q**3;E=X*Y
    k=v['eta']+v['zeta'];c=k*Y+v['eta'];a=E+Y;H=4*a+3;Dlt=a*a+H
    dd=X+a*c+(v['rho']+v['sigma'])*H
    C=q-v['alpha']-v['fixed_2d'];W=C-v['Z'];kap=v['fixed_2d_plus_b']+v['delta']*Dlt
    mu=W+a*kap+v['rho']*H
    rr=(q*q-v['Z']-q*v['F'])*(q*q-1)+(v['MC']+q*v['MF'])*v['Jrep'];L=E*k*Y
    f,r=v['f'],v['r'];icc=(v['i']*c*c)**2
    residuals=[(v['Kconstant']+X)*C-v['F']-v['zquot']*(q-1),v['r']-rr,
       L*(L+k)-v['tau']**2+1,k-r-1-v['h']*E,dd*dd-1-Dlt*c*c,
       icc-Dlt*(f*f-1),icc*((v['j']*c-r)**2-v['y_aux']**2)-1+v['y_aux']**2,
       v['j']*c-r-v['o']*f+c,mu*mu-1-Dlt*kap*kap]
    actual=[env[l]-env[r] for l,r in p['comparisons']]
    if residuals!=actual:raise ValueError('Displayed residual mismatch')
print(json.dumps({'status':'PASS','assignments':64,'residual_comparisons':576,
 'scope':'Finite algebra tests, not admissible compiler coefficients or a formal theorem'},indent=2))
