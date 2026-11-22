"""Draw the actual lower-bound witnesses and an illustrative placement."""
from pathlib import Path
import re
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.spatial import ConvexHull
from scipy.spatial.transform import Rotation

def main():
    work=Path(__file__).resolve().parent
    src=(work/'witness.hpp').read_text()
    V=np.array([list(map(int,x)) for x in re.findall(r"\{(-?\d+), (-?\d+), (-?\d+)\}",src)])/1e7
    angles=[-2.55549,-.57967,.26193]
    screen=V@Rotation.from_rotvec(angles).as_matrix()[:,:2]
    hull=screen[ConvexHull(screen).vertices]
    chord=np.array([[-.43892/2,.036],[.43892/2,.036]])
    united=np.vstack((hull,chord));united=united[ConvexHull(united).vertices]
    fig=plt.figure(figsize=(8.1,2.3))
    ax=fig.add_axes([.01,-.04,.34,1.08],projection='3d')
    ax.view_init(elev=75,azim=-50);ax.set_proj_type('ortho')
    ax.plot_trisurf(V[:,0],V[:,1],V[:,2],triangles=ConvexHull(V).simplices,color='#88b8b1',alpha=.08,edgecolor='none',shade=False)
    ax.plot(*V.T,color='#116a70',lw=2.1,zorder=20)
    ax.scatter(*V[0].T,color='#9d471b',s=16)
    ax.scatter(*V[-1].T,color='#116a70',s=16)
    ax.set_box_aspect((1,1,1));ax.set_axis_off()
    ax=fig.add_axes([.37,.11,.58,.80]);ax.set_aspect('equal')
    ax.fill(*united.T,facecolor='#f6eade',edgecolor='#ba8049',linewidth=1.2)
    ax.fill(*hull.T,facecolor='#c2ded9',edgecolor='#1d736e',linewidth=1.)
    ax.plot(*screen.T,color='#347e79',alpha=.7,lw=.90)
    ax.plot(*chord.T,color='#9d471b',lw=2.0,marker='o',ms=3)
    ax.set_axis_off()
    fig.text(.18,.025,'Spatial test path',ha='center',color='#28494b',fontsize=9)
    fig.text(.65,.025,'One projection and a chord of length 0.43892',ha='center',color='#28494b',fontsize=9)
    fig.savefig(work/'shadow.pdf')
if __name__=='__main__':
    main()
