#!/usr/bin/env python3
"""Render the exact witnesses; floating point is used for drawing only."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection,Line3DCollection
from exact_sections import solids,edges,supporting_faces,section,WITNESSES,G

ROOT=Path(__file__).resolve().parents[1]
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'pdf.fonttype':42})
names=['tetrahedron','cube','octahedron','icosahedron','dodecahedron']
labels=['Equilateral triangle','Diagonal rectangle','Equatorial square','Nonregular hexagon','Regular decagon']
formulas=[r'$\frac{\sqrt{3}}{4}a^2$',r'$\sqrt{2}\,a^2$',r'$a^2$',r'$\frac{2+\sqrt{5}}{2}a^2$',r'$\frac{5}{16}\sqrt{130+58\sqrt{5}}\,a^2$']
views=[(18,225),(23,40),(25,-35),(25,-55),(20,60)]
fig=plt.figure(figsize=(13.8,6.5),facecolor='white')
for j,(name,V) in enumerate((x,solids()[x]) for x in names):
    n,t,A2,e2=WITNESSES[name]
    unit=1/float(e2)**.5
    Vn=np.array([[float(x)*unit for x in v] for v in V])
    E=edges(V); faces=supporting_faces(V)
    Q=section(V,n,t,E)
    Qn=np.array([[float(x)*unit for x in v] for v in Q])
    ax=fig.add_subplot(2,5,j+1,projection='3d')
    ax.add_collection3d(Poly3DCollection([Vn[f] for f in faces],facecolors='#c8d5dc',edgecolors='none',alpha=.065))
    ax.add_collection3d(Line3DCollection([[Vn[i],Vn[k]] for i,k in E],colors='#758792',linewidths=.7,alpha=.8))
    ax.add_collection3d(Poly3DCollection([Qn],facecolors='#148b8c',edgecolors='#075b63',linewidths=1.1,alpha=.82))
    r=np.max(np.linalg.norm(Vn,axis=1))*1.04
    ax.set(xlim=(-r,r),ylim=(-r,r),zlim=(-r,r))
    ax.set_box_aspect((1,1,1));ax.view_init(*views[j]);ax.set_axis_off()
    ax.set_title(name.capitalize(),fontweight='bold',color='#18313c',pad=2)
    bx=fig.add_subplot(2,5,j+6)
    normal=np.array([float(G.of(x)) for x in n]);normal/=np.linalg.norm(normal)
    centroid=Qn.mean(axis=0)
    u=Qn[0]-centroid;u/=np.linalg.norm(u);w=np.cross(normal,u)
    xy=np.column_stack(((Qn-centroid)@u,(Qn-centroid)@w))
    # A horizontal long side makes the rectangle and hexagon easiest to read.
    if name in ['cube','icosahedron']:
        k=np.argmax(np.linalg.norm(np.roll(xy,-1,axis=0)-xy,axis=1))
        e=xy[(k+1)%len(xy)]-xy[k]
        ang=-np.arctan2(e[1],e[0]);c,s=np.cos(ang),np.sin(ang)
        xy=xy@np.array([[c,s],[-s,c]])
    bx.fill(xy[:,0],xy[:,1],color='#e1f0ef',ec='#08777d',lw=1.7)
    bx.scatter(xy[:,0],xy[:,1],s=10,c='#075b63',zorder=3)
    rr=max(np.ptp(xy[:,0]),np.ptp(xy[:,1]))*.65
    bx.set(xlim=(-rr,rr),ylim=(-rr,rr));bx.set_aspect('equal');bx.axis('off')
    bx.set_title(labels[j],fontsize=10,color='#18313c',pad=8)
    bx.text(.5,-.05,formulas[j],transform=bx.transAxes,ha='center',va='top',fontsize=15,color='#18313c')
fig.suptitle('Largest planar sections of the five Platonic solids',x=.5,y=.99,fontsize=19,fontweight='bold',color='#18313c')
fig.text(.5,.025,'Each solid is scaled to fit its panel. All formulas use the solid\'s edge length a.',ha='center',fontsize=9,color='#52646d')
fig.subplots_adjust(left=.012,right=.988,bottom=.16,top=.89,wspace=.08,hspace=.12)
out=ROOT/'figures';out.mkdir(exist_ok=True)
fig.savefig(out/'maximal_sections.pdf',bbox_inches='tight')
fig.savefig(out/'maximal_sections.png',dpi=190,bbox_inches='tight')
print('Wrote exact-coordinate section diagrams.')
