"""Render the values in the graph theorems. Only figure generation uses Matplotlib."""
from math import cos, pi, sqrt
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter


def band(u):
    return sqrt(4 + sqrt(8 + u + sqrt(26 - 3*u)))


def alternating(n):
    return 2*sqrt(cos(pi/n)**2 + cos(2*pi/n)**2)


def optima_figure():
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.25, 2.72))
    teal, rust, neutral = '#126960', '#A64828', '#334856'
    for ax in (left, right):
        ax.spines[['top','right']].set_visible(False)
        ax.tick_params(labelsize=8, colors=neutral, length=3)
        ax.grid(axis='y', alpha=0.22, linewidth=0.6)
        ax.set_axisbelow(True)
        ax.set_xlabel('Number of vertices', fontsize=9)
    left.set_ylabel('Minimum spectral radius', fontsize=9)
    sizes = list(range(8,32,2))
    left.plot(sizes, [alternating(n) for n in sizes], color=teal, linewidth=1.25,
              marker='o', markersize=3.8)
    left.set_title('Even cycles through 30 vertices', fontsize=10, loc='left')
    left.set_xticks([8, 12, 16, 20, 24, 28, 30])
    sizes = list(range(32,129,8))
    right.plot(sizes,[band(2*cos(8*pi/n)) for n in sizes], color=teal, linewidth=1.25,
               marker='o',markersize=3.4,label='Negative cycle sign')
    right.axhline(band(2), color=rust, ls='--', linewidth=1.3,label='Positive cycle sign')
    right.set_title('Multiples of eight from 32 vertices',fontsize=10,loc='left')
    right.set_xticks([32,56,80,104,128])
    right.set_ylim(2.7836,2.7946)
    right.set_yticks([2.784,2.787,2.790,2.793])
    right.yaxis.set_major_formatter(FormatStrFormatter('%.3f'))
    right.legend(loc='lower right',fontsize=7.8,frameon=False)
    fig.subplots_adjust(left=.085, right=.987, bottom=.18, top=.89, wspace=.32)
    fig.savefig(Path(__file__).with_name('cycle_optima.pdf'), metadata={'Title':'Exact optima on square cycles'})

def pole_figure():
    from math import acos, sin
    from matplotlib.patches import Arc, Circle

    fig, ax = plt.subplots(figsize=(6.3,2.65))
    r = 1/sqrt(3)
    ax.add_patch(Circle((0,0),r,fill=False,color='#9baeb0',lw=1))
    ax.axhline(0,color='#74818a',lw=.65)
    ax.axvline(0,color='#74818a',lw=.65)
    angle = acos(band(sqrt(2))/(2*sqrt(3)))
    ax.plot([0,r*cos(angle)],[0,r*sin(angle)],ls='--',lw=.9,color='#a64828')
    ax.add_patch(Arc((0,0),.52,.52,angle=0,theta1=0,theta2=angle*180/pi,color='#a64828'))
    for u in (-sqrt(2),sqrt(2)):
        for inner in (-1,1):
            for outer in (-1,1):
                square = 4+outer*sqrt(8+u+inner*sqrt(26-3*u))
                for sign in (-1,1):
                    theta=acos(sign*sqrt(square)/(2*sqrt(3)))
                    ax.scatter([r*cos(theta)]*2,[r*sin(theta),-r*sin(theta)],
                               s=13,color='#126960',zorder=3)
    ax.annotate('Smallest angle to the real axis', xy=(.24,.09),xytext=(.72,.16),
                fontsize=8,ha='left',color='#7e3822',arrowprops={'arrowstyle':'-','color':'#a64828','lw':.7})
    ax.text(.69,-.1,'Real axis',color='#515f65',fontsize=8)
    ax.set_xlim(-.71,1.67)
    ax.set_ylim(-.65,.65)
    ax.set_aspect('equal')
    ax.axis('off')
    fig.subplots_adjust(left=.05,right=.99,top=.99,bottom=.01)
    fig.savefig(Path(__file__).with_name('ihara_poles.pdf'),metadata={'Title':'Nontrivial Ihara poles of the minimizing 32-vertex signing'})

if __name__ == '__main__':
    optima_figure()
    pole_figure()
