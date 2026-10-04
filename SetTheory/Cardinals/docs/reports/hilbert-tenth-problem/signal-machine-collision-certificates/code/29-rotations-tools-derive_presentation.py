#!/usr/bin/env python3
"""Derive only analytic figure and summary table from frozen JSON; no physical execution."""
import argparse, json, math, os, stat, sys, hashlib
from fractions import Fraction as F
from pathlib import Path

def generate(root, out):
    root=Path(root).resolve(strict=True)
    out=Path(out)
    receipt=json.loads((root/'science/evidence/STATIC_RECEIPT.json').read_text())
    rows=[]
    for f in receipt['fixtures']:
        if f['lambda']!='1': continue
        key=(f['a'],f['b'],f['c'])
        other=[g for g in receipt['fixtures'] if (g['a'],g['b'],g['c'])==key and g['lambda']!='1']
        assert len(other)==2 and all(g['rho_squared']==f['rho_squared'] and g['events']==f['events']+24 and g['guards']==f['guards'] for g in other)
        assert all(g['distinct_nearest_points']==1 for g in [f]+other)
        rows.append(f"$({key[0]},{key[1]},{key[2]})$ & {f['Nx']} & {f['Ny']} & {f['events']} & {f['events']+24} & {f['guards']} & ${f['rho_squared']}$ \\\\")
    table=r'''\begin{center}
\small\setlength{\tabcolsep}{6pt}
\begin{tabular}{lrrrrrl}
\toprule
$(a,b,c)$ & $N_x$ & $N_y$ & $m_1$ & $m_{\ne1}$ & Guards & $\rho^2$\\\midrule
'''+ '\n'.join(rows)+r'''
\bottomrule
\end{tabular}
\end{center}
'''
    (out/'fixture-table.tex').write_text(table)
    data=json.loads((root/'science/evidence/a3_b4_c5_scale1over2.json').read_text())
    gs=[tuple(map(F,g['row'])) for g in data['guards']]
    vertices=set()
    for i,(a,b,c) in enumerate(gs):
        for d,e,f in gs[i+1:]:
            det=b*f-c*e
            if not det: continue
            x=(c*d-a*f)/det;y=(a*e-b*d)/det
            if all(al+be*x+ga*y>=0 for al,be,ga in gs): vertices.add((x,y))
    vertices=sorted(vertices,key=lambda p:math.atan2(float(p[1]),float(p[0])))
    assert len(vertices)>=3
    coords=' -- '.join(f'({float(x):.10f},{float(y):.10f})' for x,y in vertices)
    p=tuple(map(F,data['tangent_points'][0]));rho=math.sqrt(float(F(data['rho_squared'])))
    points=[];x,y=p
    for n in range(14):
        points.append((x,y));x,y=(3*x+4*y)/5,(-4*x+3*y)/5
    assert all(x*x+y*y==F(1,65) for x,y in points)
    dots='\n'.join(f'\\draw[red!75!black,fill=white,line width=0.65pt] ({float(x):.10f},{float(y):.10f}) circle[radius=0.0034];' for x,y in points)
    fig=r'''\begin{figure}[htbp]
\centering
\begin{tikzpicture}[x=10cm,y=10cm,font=\small]
\begin{scope}
\fill[gray!12] '''+coords+r''' -- cycle;
\draw[gray!70,dashed,line width=0.65pt] '''+coords+r''' -- cycle;
\fill[blue!12] (0,0) circle[radius='''+f'{rho:.10f}'+r'''];
\draw[blue!65!black,line width=0.8pt] (0,0) circle[radius='''+f'{rho:.10f}'+r'''];
\draw[-{Stealth[length=1.5mm]},gray] (-0.20,0)--(0.25,0) node[right] {$X/D$};
\draw[-{Stealth[length=1.5mm]},gray] (0,-0.20)--(0,0.37) node[above] {$Y/D$};
\fill (0,0) circle[radius=0.0015];
\draw[red!75!black,fill=white,line width=0.8pt] (0.0615384615,-0.1076923077) circle[radius=0.0035];
\node[anchor=west] at (0.078,-0.132) {$p$};
\node[anchor=north] at (0.03,-0.215) {Exact chamber and critical disk};
\end{scope}
\begin{scope}[xshift=5.45cm]
\fill[blue!12] (0,0) circle[radius='''+f'{rho:.10f}'+r'''];
\draw[blue!65!black,line width=0.8pt] (0,0) circle[radius='''+f'{rho:.10f}'+r'''];
'''+dots+r'''
\fill (0,0) circle[radius=0.0015];
\node[align=center] at (0,0.205) {Fourteen shown exclusions\\$p,\rot^{-1}p,\ldots,\rot^{-13}p$};
\node[align=center] at (0,-0.205) {The full excluded boundary set\\is countably infinite and dense};
\end{scope}
\end{tikzpicture}
\caption{Analytic normalized geometry for the new $(3,4,5)$ family, independent of $\lambda$. Dashed polygon edges are strict guards. The open disk is valid; on its critical circle exactly the entire backward orbit of $p=(4/65,-7/65)$ is excluded. The right panel shows only fourteen members of that infinite excluded set, not a complete plot of it. Vertices and orbit points are computed by exact rational formulas from the frozen fixture; this is no trajectory simulation.}
\label{fig:geometry}
\end{figure}
'''
    (out/'geometry-figure.tex').write_text(fig)
    return {'fixture_rows':len(rows),'polygon_vertices':[[str(x),str(y)] for x,y in vertices],'excluded_points_shown':14,'scope':'Exact algebraic presentation only; no physical trajectory execution'}

if __name__=='__main__':
    def require(ok,msg):
        if not ok: raise ValueError(msg)
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize,'Use python3 -I -S -B without optimization')
    root=Path(__file__).resolve().parent.parent
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',required=True);args=ap.parse_args()
    raw=args.output_dir;out=Path(raw)
    require(raw.startswith('/') and not raw.startswith('//') and str(out)==raw and all(p not in ('.','..') for p in raw.split('/')),'Canonical absolute output required')
    require(not os.path.lexists(out) and out.parent.is_dir(),'Output must be new with an existing parent')
    for p in [out.parent,*out.parent.parents]:require(not p.is_symlink(),'Symlink output ancestor')
    require(out!=root and root not in out.parents and out not in root.parents,'Output must be external')
    for p in (root/'science',root/'science/evidence'):require(p.is_dir() and not p.is_symlink(),'Evidence directory symlink')
    for name,pin in {'STATIC_RECEIPT.json':'a0a4cdb02368b994a64f9ac96e5bd3a2966d804632b5f69b268318f1c474519f','a3_b4_c5_scale1over2.json':'dbf808b92562f5a4f68f21444ed9cd7a166772c30814684bbdcd094d790945aa'}.items():
        p=root/'science/evidence'/name
        require(stat.S_ISREG(p.lstat().st_mode) and p.stat().st_nlink==1,'Regular single-link evidence required')
        require(hashlib.sha256(p.read_bytes()).hexdigest()==pin,'Evidence pin mismatch')
    out.mkdir(mode=0o700)
    receipt=generate(root,out)
    (out/'PRESENTATION_RECEIPT.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))
