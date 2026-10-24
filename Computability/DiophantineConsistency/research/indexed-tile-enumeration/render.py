#!/usr/bin/env python3
"""Render a complete standalone current-front page with directly indexed tiles."""
import argparse
from hashlib import sha256
import json,re,subprocess
import tempfile
import sys
sys.dont_write_bytecode=True
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/one-page-index-weight10'
def need(ok,why):
    if not ok:raise ValueError(why)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    for name,h in json.loads((HERE/'SOURCE_PINS.json').read_bytes())['files'].items():need(sha256((ROOT/name).read_bytes()).hexdigest()==h,'whole frozen dependency '+name)
    source=(BASE/'equation.tex').read_text();tex=source.replace(r'\sum_{t\in\mathcal T}v(t)x^{\varrho(t)}',r'\sum_{i=0}^{942}v(t_i)x^i')
    start=tex.index(r'\textbf{The 943 fixed tiles and their ranks.}');stop=tex.index(r'\textbf{A closed decoder for the 430 actions.}',start)
    table=r'''\textbf{The 943 indexed fixed tiles.}
Use the actions $u_j,v_j,d_j$ decoded below. Let
\[
\begin{gathered}
h(q,b)=2(q+1)+b,\quad
\mathcal R=\{u_j:d_j=1,\ 0\le j<430\},\\
\mathcal L=\{u_j:d_j=0,\ 0\le j<430\},\\
r_q=6+|\mathcal R\cap\rg0{q-1}|,\quad
l_q=205+|\mathcal L\cap\rg0{q-1}|.
\end{gathered}
\]
An interval ending at $-1$ is empty. The table defines $t_i$ for
$0\le i\le942$; all index ranges are fixed:
\[
\setlength{\arraycolsep}{1.4pt}\begin{array}{c|l}
\text{index }i&\text{tile }t_i=(w,n,e,s)\\\hline
0,1&(2,435,3,1),\ (5,0,0,0)\\
j+2\ (j=2q+b<430)&((1-d_j)l_{u_j},h(q,b),d_jr_{u_j},v_j)\\
432+b\ (b=0,1)&(0,h(215,b),0,h(215,b))\\
434+b\ (b=0,1)&(0,b,0,b)\\
424+2r_q+b\ (q\in\mathcal R,b=0,1)&(r_q,b,0,h(q,b))\\
424+2l_q+b\ (q\in\mathcal L,b=0,1)&(0,b,l_q,h(q,b))\\
924+j\ (0\le j<4)&(0,j+430\fl{j/2},0,438)\\
928&(2,434,2,0)\\
929&(3,436,4,4)\\
930&(4,436,4,0)\\
497+t\ (t=434,435,436)&(1,438,1,t)\\
\substack{934+3a+b-6\fl{a/4}\\a\in\{0,1,4\},\ b=0,1,2}&(a,437,b,437)
\end{array}
\]
For $t=(w,n,e,s)$ put
\[
v(t)=w+2^8n+2^{17}e+2^{25}s+127\,2^{34}.
\]

'''
    tex=tex[:start]+table+tex[stop:]
    need(all(token not in tex for token in [r'\kappa(t)',r'\varrho',r'\mathcal T\prime',r'\mathcal T\setminus']),'all sorting/rank definitions eliminated')
    with tempfile.TemporaryDirectory(prefix='indexed-tiles-render-') as directory:
        out=Path(directory);(out/'equation.tex').write_text(tex)
        result=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','equation.tex'],cwd=out,capture_output=True,text=True)
        need(result.returncode==0,'full standalone TeX render')
        subprocess.run(['pdftotext','-raw',str(out/'equation.pdf'),str(out/'equation.txt')],check=True)
        info=subprocess.check_output(['pdfinfo',str(out/'equation.pdf')],text=True)
        text=(out/'equation.txt').read_text();old=(BASE/'equation.txt').read_text()
        def recipe(t):return t[t.index('The four fixed integers.'):t.index('The ordinary state/color')]
        nonwhite=lambda s:sum(not c.isspace() for c in s)
        compact=lambda s:''.join(s.split())
        literal=(HERE/'SEED.txt').read_text().strip();need(literal in compact(text) and '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz' in compact(text),'every printed seed/alphabet character retained')
        need(tex[:tex.index(r'\textbf{The four fixed integers.}')]==source[:source.index(r'\textbf{The four fixed integers.}')],'entire freeport arithmetic front unchanged')
        metric=dict(status='PASS',optimized_python=bool(sys.flags.optimize),baseline='candidates/one-page-index-weight10',pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1]),overfull='Overfull' in result.stdout,recipe_nonwhite=nonwhite(recipe(text)),baseline_recipe_nonwhite=nonwhite(recipe(old)),whole_page_nonwhite=nonwhite(text),baseline_page_nonwhite=nonwhite(old),net_recipe_change=nonwhite(recipe(text))-nonwhite(recipe(old)),net_page_change=nonwhite(text)-nonwhite(old),tex_nonwhite=nonwhite(tex),baseline_tex_nonwhite=nonwhite(source),complete_current_front_unchanged=True,all436seed_symbols_exact=True,all62alphabet_symbols_exact=True,pdf_sha256=sha256((out/'equation.pdf').read_bytes()).hexdigest())
        need(metric['pages']==1 and not metric['overfull'] and metric['net_recipe_change']==metric['net_page_change']==-50,'full onepage/recipe size comparison')
        for name,blob in [('equation.tex',tex.encode()),('equation.pdf',(out/'equation.pdf').read_bytes()),('equation.txt',text.encode())]:
            target=HERE/name
            if args.check:need(target.read_bytes()==blob,'deterministic whole standalone artifact '+name)
            else:target.write_bytes(blob)
    print(json.dumps(metric,indent=2,sort_keys=True))
if __name__=='__main__':main()
