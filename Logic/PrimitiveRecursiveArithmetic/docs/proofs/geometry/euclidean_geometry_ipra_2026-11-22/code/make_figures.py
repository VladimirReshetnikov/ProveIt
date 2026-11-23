#!/usr/bin/env python3
"""Draw explanatory figures from exact formulas/certified solid vertices.

Floating point is used only for rendering; no numerical plot is proof evidence.
Run from any directory. Output figures are part of the report.
"""
from pathlib import Path
import json, math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Polygon

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False})
BLUE, TEAL, GOLD, GREY = '#234b71','#168a89','#d18b27','#8995a3'

def finish(fig, name):
    fig.savefig(OUT/(name+'.pdf'), bbox_inches='tight')
    fig.savefig(OUT/(name+'.png'), bbox_inches='tight', dpi=170)
    plt.close(fig)

def triangle_centers():
    fig, axes = plt.subplots(1,2,figsize=(10.8,4.5))
    A,B,C=np.array([0.,0.]),np.array([6.,0.]),np.array([2.,4.])
    O,H,G,N=np.array([3.,1.]),np.array([2.,2.]),np.array([8/3,4/3]),np.array([2.5,1.5])
    ax=axes[0]
    ax.add_patch(Circle(O, math.sqrt(10),fill=False,edgecolor=BLUE,lw=1.3))
    ax.add_patch(Circle(N,math.sqrt(10)/2,fill=False,edgecolor=TEAL,lw=1.5,ls='--'))
    ax.add_patch(Polygon([A,B,C],closed=True,fill=False,edgecolor=BLUE,lw=2))
    ax.plot([3.5,1.5],[.5,2.5],color=GOLD,lw=1.3)
    for p,q in [(C,np.array([2.,0.])),(A,np.array([3.,3.])),(B,np.array([1.2,2.4]))]:
        ax.plot(*np.array([p,q]).T,color=GREY,lw=.8,ls=':')
    for label,p,off in [('A',A,(-10,-15)),('B',B,(5,-15)),('C',C,(-2,8)),
                         ('O',O,(9,-9)),('H',H,(-15,5)),('G',G,(10,6))]:
        ax.scatter(*p,color=BLUE if label in 'ABC' else GOLD,s=20,zorder=5)
        ax.annotate(label,p,xytext=off,textcoords='offset points')
    for p in [(A+B)/2,(B+C)/2,(C+A)/2,(H+A)/2,(H+B)/2,(H+C)/2,np.array([2.,0.]),np.array([3.,3.]),np.array([1.2,2.4])]:
        ax.scatter(*p,color=TEAL,s=14,zorder=4)
    ax.set_title('Triangle centers and the nine-point circle',loc='left',fontweight='bold',pad=14)
    ax.set_aspect('equal'); ax.set_xlim(-.6,6.6); ax.set_ylim(-2.5,4.6);ax.axis('off')
    ax.text(.5,-.06,r'$O=(3,1),\ H=(2,2),\ G=(8/3,4/3)$',transform=ax.transAxes,ha='center')
    ax=axes[1]
    ax.add_patch(Circle((0,0),2,fill=False,edgecolor=BLUE,lw=2))
    for y,label,col in [(.9,'two intersections',TEAL),(2,'one tangent point',GOLD),(2.65,'no intersection',GREY)]:
        ax.plot([-2.8,2.8],[y,y],color=col,lw=1.5)
        ax.text(-2.8,y+.11,label,color=col)
    x=math.sqrt(4-.9**2)
    ax.scatter([-x,x],[.9,.9],color=TEAL,s=30,zorder=4)
    ax.scatter([0],[2],color=GOLD,s=30,zorder=4)
    ax.scatter([0],[0],color=BLUE,s=14)
    ax.annotate('O',(0,0),xytext=(7,-2),textcoords='offset points')
    ax.set_title('A finite discriminant controls the branches',loc='left',fontweight='bold',pad=14)
    ax.set_aspect('equal');ax.set_xlim(-3,3);ax.set_ylim(-2.5,3.2);ax.axis('off')
    ax.text(.5,-.06,r'$x^2+y^2=4:\quad x^2=4-y^2$',transform=ax.transAxes,ha='center')
    fig.tight_layout(w_pad=2.2)
    finish(fig,'centers-and-intersections')

if __name__=='__main__':
    triangle_centers()
    print('Wrote figures/centers-and-intersections.pdf and .png')
