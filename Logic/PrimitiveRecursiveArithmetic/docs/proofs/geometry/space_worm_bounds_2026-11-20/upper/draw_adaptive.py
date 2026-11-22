"""Draw two certified prism placements. Optional dependencies: NumPy, SciPy, Matplotlib."""

from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection
from matplotlib.colors import to_rgb
import numpy as np
from scipy.spatial import ConvexHull
from scipy.spatial.transform import Rotation
from check_adaptive import DIR, SCALE, points

def unit(v):
    return np.array(v, dtype=float) / np.linalg.norm(v)

def base_vertices():
    t = np.array([-631/58, -1, 7/16, 37/56])
    normals = np.column_stack(((1-t*t)/(1+t*t), 2*t/(1+t*t)))
    d = np.array([0., 0., 130783/250000, 446199/1000000])
    vertices = []
    for j in range(4):
        lines = [j, (j+1)%4]
        vertices.append(np.linalg.solve(normals[lines], d[lines]))
    return np.array(vertices)

def main():
    hull_points = np.array(points(),dtype=float)/SCALE
    center = np.array([0.17, 0.13, 0.07])
    hull_points = center + (1 + 20/SCALE)*(hull_points-center)
    boundary = ConvexHull(hull_points)
    poses = np.array(json.loads((DIR/"poses.json").read_text()))/SCALE
    camera = unit([0.92, -1.90, 1.10])
    right = unit(np.cross([0., 0., 1.], camera))
    up = np.cross(camera, right)
    screen = np.column_stack((right, up))
    projected = hull_points @ screen
    outline = ConvexHull(projected).vertices
    visible = boundary.equations[:,:3] @ camera > 1e-10
    triangles = projected[boundary.simplices[visible]]
    light = unit([-0.62, -0.52, 1.0])
    shading = .19 + .48*np.clip(boundary.equations[visible,:3] @ light, 0, 1)
    def colors(tone):
        return (1-shading[:,None])+shading[:,None]*np.array(to_rgb(tone))
    fig,axes = plt.subplots(1,2,figsize=(8.2,2.35))
    fig.subplots_adjust(left=.015,right=.985,bottom=.03,top=.83,wspace=.10)
    base = base_vertices()
    polygon_edges = [(0,1),(1,2),(2,3),(3,0)]
    for ax, index, color,label in zip(axes,[10,20],["#186776","#9f4826"],
                                    ["Upright placement","Turned placement"]):
        t,*row = poses[index]
        p,h = (1-t*t)/(1+t*t), 2*t/(3*(1+t*t))
        xyz = np.column_stack((np.tile(base*p, (2,1)), np.repeat([0,h],4)))
        prism = Rotation.from_quat(row[:4]).apply(xyz)+row[4:]
        vertices = prism @ screen
        ax.add_collection(PolyCollection(triangles,facecolors=colors("#a6b8b7"),
                          edgecolors="face",linewidths=.1,antialiased=False,
                          rasterized=True,zorder=1))
        outline_loop = np.r_[outline,outline[:1]]
        ax.plot(*projected[outline_loop].T,color="#708382",lw=.65,zorder=2)
        normals=np.cross(prism[1]-prism[0],prism[2]-prism[0])
        active_face=vertices[:4] if normals @ camera < 0 else vertices[4:]
        ax.fill(*active_face.T,facecolor=color,alpha=.10,zorder=3)
        for i,j in polygon_edges:
            for shift in [0,4]:
                ax.plot(*vertices[[i+shift,j+shift]].T,color=color,lw=1.0,
                        alpha=.94,zorder=4)
        for i in range(4):
            ax.plot(*vertices[[i,i+4]].T,color=color,lw=1.0,zorder=4)
        ax.set_aspect("equal")
        xymin,xymax=projected.min(0),projected.max(0)
        ax.set_xlim(xymin[0]-.035,xymax[0]+.035)
        ax.set_ylim(xymin[1]-.022,xymax[1]+.025)
        ax.set_axis_off()
        ax.set_title(label+"\n"+rf"$h={h:.3f},\quad p={p:.3f}$",
                     fontsize=10.5,color="#233b40",pad=3,linespacing=1.25)
    fig.savefig(DIR/"adaptive_cover.pdf",dpi=240)
    plt.close(fig)

if __name__=="__main__":
    main()
