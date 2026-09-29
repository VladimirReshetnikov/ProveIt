"""Regenerate the two separate illustrative figures from retained CSV data."""
from pathlib import Path
import csv
import math
import matplotlib.pyplot as plt

# Export setting: keep text searchable without Type 3 glyphs.
plt.rcParams["pdf.fonttype"] = 42

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    with (ROOT/'data'/'scalar_numerics.csv').open(newline='') as f:
        rows = sorted((r for r in csv.DictReader(f) if int(r['m']) >= 100),
                      key=lambda r: int(r['m']))
    if not rows:
        raise ValueError('No numerical rows with m >= 100 were found')
    m = [int(r['m']) for r in rows]
    lo = [float(r['E_lower']) for r in rows]
    hi = [float(r['E_upper']) for r in rows]
    width = [float(r['corridor_width']) for r in rows]
    output = ROOT/'figures'
    output.mkdir(exist_ok=True)
    fig, ax = plt.subplots(figsize=(8.0,4.7))
    ax.semilogx(m,lo,label='Lower bound for the centered remainder')
    ax.semilogx(m,hi,linestyle='--',label='Upper bound for the centered remainder')
    ax.axhline(2*math.log(math.pi),linestyle=':',label=r'Proved limit: $2\log\pi$')
    ax.set_xlabel(r'Adjacency bound $m$')
    ax.set_ylabel(r'$m(4-\alpha_m)-2\log m-4\log\log m$')
    ax.set_title('A narrowing corridor, but very slow convergence')
    ax.legend(fontsize=9)
    ax.grid(True,alpha=.25)
    fig.tight_layout()
    fig.savefig(output/'remainder_corridor.pdf')
    fig.savefig(output/'remainder_corridor.png',dpi=180)
    plt.close(fig)
    fig, ax = plt.subplots(figsize=(8.0,4.7))
    ax.loglog(m,width,label='Computed scalar-corridor width')
    ax.loglog(m,[math.log(v)**2/v**2 for v in m],linestyle='--',
              label=r'Reference scale: $(\log m)^2/m^2$')
    ax.set_xlabel(r'Adjacency bound $m$')
    ax.set_ylabel('Width in the growth constant')
    ax.set_title('The scalar bounds capture much finer accuracy')
    ax.legend(fontsize=9)
    ax.grid(True,alpha=.25)
    fig.tight_layout()
    fig.savefig(output/'corridor_width.pdf')
    fig.savefig(output/'corridor_width.png',dpi=180)
    plt.close(fig)

if __name__ == '__main__':
    main()
