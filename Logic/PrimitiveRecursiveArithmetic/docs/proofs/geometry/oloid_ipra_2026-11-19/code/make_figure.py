"""Generate the two geometric views used in the paper, in unit-radius coordinates."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

def patch(t, s):
    co, si = (1-t*t)/(1+t*t), 2*t/(1+t*t)
    q = 1-.75*si**2
    a, b = .5-2*q, (1-q)/(2*q)
    return (1-s)*a+s*b, (1-s)*np.sqrt(3*q)*si, s*np.sqrt(3)*co/(2*q)

fig = plt.figure(figsize=(6.9, 2.7))
ax = fig.add_subplot(1, 2, 1, projection="3d", computed_zorder=False)
t, s = np.meshgrid(np.linspace(0,1,81),np.array([0.,1.]))
X, Y, Z = patch(t, s)
for sy in (-1,1):
    for sz in (-1,1):
        ax.plot_surface(X, sy*Y,sz*Z,color="#abcfca",edgecolor="none", alpha=.54,
                        shade=True, rcount=2, ccount=81)
        for u in np.linspace(0,1,12):
            x,y,z=patch(u,np.array([0.,1.]))
            ax.plot(x, sy*y, sz*z,color="#447876",alpha=.55,lw=.55)
ang=np.linspace(0,2*np.pi,300)
ax.plot(-.5+np.cos(ang),np.sin(ang),0*ang,color="#8c422e",lw=1.4)
ax.plot(.5+np.cos(ang),0*ang,np.sin(ang),color="#165069",lw=1.4)
ax.plot([-1.65,1.85],[0,0],[0,0],ls="--",color="#353c42",lw=.85)
ax.text(1.87,0,0,"x",fontsize=12)
ax.set(xlim=(-1.6,1.8),ylim=(-1.04,1.04),zlim=(-1.04,1.04))
ax.set_box_aspect((3.4,2.08,2.08),zoom=1.25)
ax.view_init(elev=27,azim=-58)
ax.set_axis_off()
ax.set_title("Generating circles and rulings",fontsize=10, y=1.03)

right = fig.add_subplot(1, 2, 2)
x0=.5
qhi=1/(1+2*x0)
tmin=np.sqrt(4*(1-qhi)/3)/(1+np.sqrt((4*qhi-1)/3))
t=np.linspace(tmin,1,200)
q=1-.75*(2*t/(1+t*t))**2
s=(x0-(.5-2*q))/((1-q)/(2*q)-(.5-2*q))
_, y, z=patch(t,s)
right.fill_between(y,z,color="#c0dcd5")
right.plot(y,z,color="#165069",lw=1.7)
for i in np.linspace(5,195,12,dtype=int):
    right.plot([y[i],y[i]],[0,z[i]],color="#588d85",lw=.65)
right.set(xlim=(0,.64),ylim=(0,1.12),xlabel="transverse coordinate  y",ylabel="height  z")
right.set_title("Vertical columns at  x = 1/2", fontsize=10)
right.spines[["top","right"]].set_visible(False)
right.tick_params(labelsize=8)
right.set_aspect(.63)
fig.subplots_adjust(left=.03,right=.96,bottom=.20,top=.86,wspace=.04)
fig.savefig(Path(__file__).resolve().parent.parent/"figures"/"geometry.pdf",bbox_inches="tight",pad_inches=.05)
