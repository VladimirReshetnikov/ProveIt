"""Numerical axis stationary-point exploration; uniqueness is proved separately."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=55
C=lambda b:-2*mp.im(mp.j*mp.polylog(b,mp.j)/(1-mp.j))
r=mp.findroot(lambda b:mp.diff(C,b),(mp.mpf('1.2'),mp.mpf('1.6')))
row=dict(working_precision=55,axis_stationary_inner_order=mp.nstr(r,48),
 axis_Gaussian_constant=mp.nstr(C(r),48),second_derivative=mp.nstr(mp.diff(C,r,2),35),
 samples=[dict(b=mp.nstr(b,15),constant=mp.nstr(C(b),35)) for b in
          map(mp.mpf,['0.01','0.25','0.5','1','1.25','1.5','2','3','5','10'])],
 scope='Floating-point one-dimensional axis exploration. Local stationary-point diagnostics do not prove uniqueness or a global maximum.')
B=Path(__file__).resolve().parents[1]
(B/'verification/Gaussian-axis-exploration.json').write_text(json.dumps(row,indent=2)+'\n',encoding='utf-8')
print('Axis stationary order',row['axis_stationary_inner_order'],'constant',row['axis_Gaussian_constant'])
