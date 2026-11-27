#!/usr/bin/env python3
"""Regenerate the static scientific illustration from exact prime formulas."""
from pathlib import Path
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_resonance import kernel, centered_second_difference, arithmetic_matrix

mp.mp.dps=60
out=Path(__file__).resolve().parents[1]/'figures'
out.mkdir(exist_ok=True)
plt.rcParams.update({'font.size':10,'axes.titlesize':11,'font.family':'DejaVu Sans',
                     'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig,(ax,bx)=plt.subplots(1,2,figsize=(10,4.1),gridspec_kw={'width_ratios':[1.25,1]})
v=np.linspace(-1.65,1.65,181)
J=float(mp.log(2)/mp.sqrt(2))
ax.plot(v,J*np.maximum(0,1-np.abs(v)),color='#17333D',lw=2.6,label='Proved limit')
for ht,color in [('0.04','#D79C3C'),('0.01','#5695A3'),('0.002','#087F8C')]:
    h=mp.mpf(ht)
    y=[float(-centered_second_difference(mp.log(2)+h*mp.mpf(str(x)),h)/h) for x in v]
    ax.plot(v,y,lw=1.4,color=color,label=f'h = {ht}',alpha=.9)
ax.set(title='A triangular resonance at log 2',xlabel='Offset v in log 2 + v h',
       ylabel=r'$-[2K(a)-K(a+h)-K(a-h)]/h$')
ax.grid(alpha=.15)
ax.legend(frameon=False,fontsize=9)
A=arithmetic_matrix(8)
arr=np.array([[float(A[i,j]) for j in range(8)] for i in range(8)])
im=bx.imshow(arr,cmap='YlGnBu',vmin=0,vmax=float(np.max(arr)))
bx.set_xticks(range(8),range(1,9));bx.set_yticks(range(8),range(1,9))
bx.set(title='Prime-power ratio matrix, N = 8',xlabel='Integer j',ylabel='Integer i')
for i in range(8):
    for j in range(8):
        if arr[i,j]>0:
            bx.text(j,i,f'{arr[i,j]:.2f}',ha='center',va='center',fontsize=8,
                    color='white' if arr[i,j]>.48 else '#17333D')
fig.colorbar(im,ax=bx,fraction=.045,pad=.035,label='Edge weight')
fig.tight_layout(pad=1.6,w_pad=2)
fig.savefig(out/'resonance_and_matrix.pdf',bbox_inches='tight')
fig.savefig(out/'resonance_and_matrix.png',dpi=180,bbox_inches='tight')
print('Created resonance_and_matrix.pdf and .png')
