#!/usr/bin/env python3
"""Render exact Platonic model certificates as orthographic vector diagrams.

Floating point is used ONLY for drawing. All faces and incidences come from
certificates.json, generated and checked by exact_models.py.
"""
from pathlib import Path
import json
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

ROOT=Path(__file__).resolve().parent.parent
PHI=(1+math.sqrt(5))/2

def scalar(x):
    from fractions import Fraction
    return float(Fraction(x[0]))+float(Fraction(x[1]))*PHI

def normalized(x):
    x=np.asarray(x,dtype=float)
    return x/np.linalg.norm(x)

def main():
    data=json.loads((ROOT/'certificates'/'certificates.json').read_text())
    models={r['name']:r for r in data['solids']}
    names=['tetrahedron','cube','octahedron','dodecahedron','icosahedron']
    titles=['Tetrahedron','Cube','Octahedron','Dodecahedron','Icosahedron']
    # A common orthographic camera makes the diagrams directly comparable.
    toward=normalized([5.4,3.5,2.8])
    right=normalized(np.cross([0,0,1],toward))
    up=normalized(np.cross(toward,right))
    light=normalized([2.0,-1.5,5.0])
    palettes=['#80A5BF','#8BAE9A','#A6A0C4','#D1B379','#7CAAB0']
    fig=plt.figure(figsize=(8.2,6.2))
    grid=fig.add_gridspec(2,6,left=.025,right=.975,top=.99,bottom=.015,wspace=.30,hspace=.10)
    axes=[fig.add_subplot(grid[0,0:2]),fig.add_subplot(grid[0,2:4]),
          fig.add_subplot(grid[0,4:6]),fig.add_subplot(grid[1,1:3]),
          fig.add_subplot(grid[1,3:5])]
    fig.patch.set_facecolor('white')
    for ax,name,title,base in zip(axes,names,titles,palettes):
        rec=models[name]
        xyz=np.array([[scalar(x) for x in v] for v in rec['vertices']])
        xyz/=max(np.linalg.norm(v) for v in xyz)
        xy=np.column_stack((xyz@right,xyz@up))
        rgb=np.array(matplotlib.colors.to_rgb(base))
        face_data=[]
        for ids in rec['faces']:
            points=xyz[ids]
            normal=normalized(np.cross(points[1]-points[0],points[2]-points[0]))
            center=points.mean(axis=0)
            if np.dot(normal,center)<0: normal=-normal
            brightness=.72+.28*(.5+.5*np.dot(normal,light))
            color=np.clip(rgb*brightness+.10*(1-brightness),0,1)
            face_data.append((np.dot(center,toward),ids,color))
        for depth,ids,color in sorted(face_data,key=lambda row:row[0]):
            ax.add_patch(Polygon(xy[ids],closed=True,facecolor=color,
                                 edgecolor='#304656',linewidth=.85,
                                 joinstyle='round',zorder=depth+3))
        ax.text(0,1.32,title,ha='center',va='center',fontsize=12.5,
                fontweight='semibold',color='#17354A',family='DejaVu Sans')
        ax.text(0,-1.20,rf'$\{{{rec["p"]},{rec["q"]}\}}$',ha='center',va='center',
                fontsize=12.5,color='#17354A')
        ax.text(0,-1.51,f'{rec["V"]} vertices  ·  {rec["E"]} edges  ·  {rec["F"]} faces',
                ha='center',va='center',fontsize=8.1,color='#3D4D57',family='DejaVu Sans')
        ax.set_xlim(-1.14,1.14);ax.set_ylim(-1.70,1.53)
        ax.set_aspect('equal');ax.axis('off')
    fig.savefig(ROOT/'paper'/'platonic_models.pdf',bbox_inches='tight',pad_inches=.025,
                metadata={'Title':'The five Platonic solids: exact coordinate models',
                          'Author':'OpenAI for Vladimir Reshetnikov',
                          'Subject':'Orthographic projections of exact algebraic models'})
    fig.savefig(ROOT/'paper'/'platonic_models.png',dpi=240,bbox_inches='tight',pad_inches=.025)
    print('Wrote platonic_models.pdf and platonic_models.png')

if __name__=='__main__': main()
