#!/usr/bin/env python3
"""Regenerate the finite mathematical tables in report.tex from supplied data.

Standard library only. This is an authoring helper, not the mathematical verifier.
"""
from pathlib import Path
from collections import Counter
import json

ROOT = Path(__file__).resolve().parent
GEN = ROOT / 'generated'

def read(rel):
    return json.loads((ROOT / rel).read_text())

def monomial(vs):
    c = Counter(vs)
    return ''.join('x_{%d}' % v + ('^{%d}' % e if e > 1 else '')
                   for v, e in sorted(c.items()))

def term(c, vs, first=False):
    if not c:
        return ''
    sign = '-' if c < 0 else ('' if first else '+')
    a = abs(c)
    body = (str(a) if a != 1 or not vs else '') + monomial(vs)
    return sign + body

def poly(ts):
    return ''.join(term(c,vs,i==0) for i,(c,vs) in enumerate(ts)) or '0'

def chunks(ts, budget=72):
    result=[]; current=[]; cost=0
    for i,(c,vs) in enumerate(ts):
        s=term(c,vs,i==0)
        weight=1+len(str(abs(c)))+4*len(vs)
        if current and cost+weight>budget:
            result.append(''.join(current));current=[];cost=0
        current.append(s);cost+=weight
    if current: result.append(''.join(current))
    return result or ['0']

def write(name, s):
    (GEN/name).write_text(s.rstrip()+'\n')

def main():
    GEN.mkdir(exist_ok=True)
    eq=read('direct/equations/integer84_degree2097808.json')
    control=read('direct/equations/control_integer85_degree2097808.json')
    m=eq['metrics']; cm=control['metrics']
    # The JSON metrics schema is retained verbatim; the constants here are
    # independently checked against the actual input and residual lists.
    nv=len(eq['variables']); nr=len(eq['residual_roots'])
    deg=eq['degree_certificate'].get('degree',m.get('exact_degree'))
    if deg is None: deg=m.get('degree')
    if isinstance(deg,dict): deg=deg.get('exact_degree')
    if nv!=84 or nr!=23 or deg!=2097808: raise ValueError('Unexpected direct endpoint')
    ops=m.get('binary_operations',m.get('operations'))
    cops=cm.get('binary_operations',cm.get('operations'))
    write('metrics.tex', '\\newcommand{\\DirectVars}{%d}\n'
          '\\newcommand{\\DirectRows}{%d}\n'
          '\\newcommand{\\DirectDegree}{2{,}097{,}808}\n'
          '\\newcommand{\\DirectOps}{%s}\n' % (nv,nr,ops))
    comp=r'''\begin{center}\small
\begin{tabular}{lrrrr}\toprule
Equation / route&Variables&Domain&Degree&Operations\\\midrule
Matched direct control&85&$\Z$&$2{,}097{,}808$&CONTROL\\
\textbf{Affine orientation / direct}&\textbf{84}&$\Z$&$\mathbf{2{,}097{,}808}$&\textbf{OPS}\\
Prior Carrier65&14&$\Pos$&150&65\\
\textbf{Scaled companion}&\textbf{14}&$\Pos$&\textbf{118}&\textbf{66}\\
\textbf{Ordinary companion}&\textbf{14}&$\Pos$&\textbf{94}&\textbf{67}\\\bottomrule
\end{tabular}
\end{center}
Operations mean live binary additions, subtractions, and multiplications with fixed integer leaves. The direct and native rows have different coefficient architectures; the table does not identify a single winner across all measures.'''
    write('comparison.tex',comp.replace('CONTROL',str(cops)).replace('OPS',str(ops)))
    cert=read('direct/orientation_certificate.json')
    parent=read('direct/parent206.json')
    piv=read('direct/certificates/principal84.json')['steps']
    pool=read('direct/factored_pool.json')
    out=[r'''This appendix defines the direct polynomial without an unprinted program index. All row and coordinate indices are fixed integers. First form the 145 residuals below in formal coordinates $x_0,\ldots,x_{205}$, using the affine orientation row at index 135. Then apply the 122 listed unit substitutions and sum the squares of the remaining 23 residuals. The source input map gives the 84 independent integer variables in order. These are finite polynomial abbreviations, not additional quantifiers.

\subsection{The fourteen principal pairs}
In every row $X_i=D_i+Z_i$; the entries already include all coordinate offsets. The center is $A=1+x_{132}$. The final column is the retained principal norm row.
\begin{center}\small\begin{tabular}{rrrrrr}\toprule
$i$&$D_i$&$Y_i$&$Z_i$&$k_i$&Norm row\\\midrule''']
    for i,p in enumerate(cert['pairs']):
        out.append('%d&$x_{%d}$&$%s$&$%s$&$%s$&%d\\\\' %
                   (i,p['D'],poly(p['Y']),poly(p['Z']),poly(p['index']),p['norm_row']))
    out.extend([r'\bottomrule\end{tabular}\end{center}',r'''\subsection{The quadratic source rows}
The orientation row 135 is defined separately by
\[
R_{135}=\sum_{i=0}^{13}\bigl[1-D_i-Z_i+(Y_i-k_i)^2\bigr]-x_{132}x_{193}.
\]
Every other row below is copied from the literal parent. Set each displayed polynomial equal to zero when considering the intermediate system. In the final single polynomial, only the residuals left after the fixed substitutions are squared.
\begingroup\small
\begin{align*}'''])
    for i,r in enumerate(parent['residuals'][:144]):
        if i==135: continue
        ps=chunks(r['terms'])
        out.append('R_{%d}&=%s' % (i,ps[0]) + (r'\\' if len(ps)>1 else r'\\[2pt]'))
        for q,s in enumerate(ps[1:]):
            out.append(r'&\quad '+s+(r'\\[2pt]' if q==len(ps)-2 else r'\\'))
    out.extend([r'\end{align*}\endgroup',r'''\subsection{The five-base pooling row}
For each block $j=0,\ldots,4$, let $b_j$ be its base and take the fixed request list in the table. For a request $(D,Y,Z,m)$ define
\[
e_{j}= (m-D)^2-Y^2-2b_jY(m-D-Z).
\]
Put $E_j=\sum e_j$ over that block and $T_j=2Ab_j-b_j^2-1$. The one remaining source row is
\[
R_{144}=\sum_{j=0}^{4}b_jE_j\prod_{\substack{0\le h\le4\\h\ne j}}T_h
-x_{205}\prod_{h=0}^{4}T_h.
\]
There is no variable-length sum here: the following 16 requests are the entire list.
\begin{center}\small\begin{tabular}{rrrrrr}\toprule
Block&$b_j$&$D$&$Y$&$Z$&$m$\\\midrule'''])
    for j,b in enumerate(pool['blocks']):
        for req in b['requests']:
            out.append('%d&$%s$&$%s$&$%s$&$%s$&$%s$\\\\'%
                       (j,poly(b['base']),poly(req['D']),poly(req['Y']),poly(req['Z']),poly(req['m'])))
    out.extend([r'\bottomrule\end{tabular}\end{center}',r'''\subsection{The exact unit substitutions}
Each pair $(r,v)$ says to solve row $R_r$ for coordinate $x_v$, whose coefficient in that row is $+1$ or $-1$, and recursively substitute its definition. The directed dependency graph is acyclic; numerical row order need not itself be a topological order. The polynomial constructor and independent verifier both check the graph. The pair $(135,142)$ is the orientation deletion.
\begingroup\small
\begin{longtable}{rr@{\qquad}rr@{\qquad}rr@{\qquad}rr}\toprule
Row&Variable&Row&Variable&Row&Variable&Row&Variable\\\midrule
\endfirsthead
\toprule Row&Variable&Row&Variable&Row&Variable&Row&Variable\\\midrule
\endhead
\midrule\multicolumn{8}{r}{Continued on the next page}\\\endfoot
\bottomrule\endlastfoot'''])
    for start in range(0,len(piv),4):
        row=[]
        for p in piv[start:start+4]:row.extend([str(p['row']),str(p['variable'])])
        row.extend(['']*(8-len(row)));out.append('&'.join(row)+r'\\')
    out.extend([r'\end{longtable}\endgroup',r'\subsection{Independent coordinates and retained residuals}',
                r'Assign $u_0,u_1,\ldots,u_{83}$ to the following source coordinate indices, in the displayed order:'])
    ids=eq['source_input_indices']
    out.append(r'\[\begin{gathered}')
    for a in range(0,len(ids),17):out.append(','.join(map(str,ids[a:a+17]))+(r'\\' if a+17<len(ids) else ''))
    out.append(r'\end{gathered}\]')
    out.append('The remaining residual row indices are')
    out.append(r'\[\begin{gathered}')
    ids=eq['retained_source_rows']
    for a in range(0,len(ids),13):out.append(','.join(map(str,ids[a:a+13]))+(r'\\' if a+13<len(ids) else ''))
    out.append(r'\end{gathered}\]')
    out.append(r'After the specified substitutions, their sum of squares is the complete polynomial $P_{84}$. The listed coordinates, rows, and pivot coefficients are checked against the literal circuit; no unresolved coefficient parameter remains.')
    write('direct_appendix.tex','\n'.join(out))
    source=(ROOT/'native/sources/block-mask2963_equation.tex').read_text()
    start=source.index(r'\textbf{The four fixed integers.}')
    end=source.index(r'\normalfont\fontsize{7.7}{8.2}\selectfont',start)
    body=source[start:end].replace(r'\textbf{The four fixed integers.}',r'\subsection*{Complete finite specification}')
    body=body.replace(r'\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily',r'\begingroup\small\ttfamily')
    body=body.replace('The alphabet, in order of digit values $0,\\ldots,61$, is\n', 'The alphabet, in order of digit values $0,\\ldots,61$, is\\par\n')
    intro=r'''The following constant recipe is retained from the current block-mask2963 page. Its symbols and fixed finite index sets define four integers only. In this appendix the source's $K$ is the front end's $K_0$, and $\beta=B-1$. The variable $x$ in the finite polynomial $\Phi(x)$ is a dummy in a constant definition; it is not an unknown of either consistency equation. The archived binary payloads have total raw size 69,685 bytes and reproduce this recipe. The ordinary native calibration is retained separately.
\begingroup\small
\newcommand{\fl}[1]{\left\lfloor#1\right\rfloor}
\newcommand{\rg}[2]{\{#1,\ldots,#2\}}
'''
    write('native_appendix.tex',intro+body+'\n\\endgroup\n')
    verification=r'''The release-level \pathcode{verify.py} runs the independent direct circuit audit, the separately written orientation/source audit, and the native companion audit. It also checks the exact report tables against the delivered data. The principal direct graph has OPS live binary operations, 23 residuals, and 84 free integer inputs. Its matched control has CONTROL operations, 24 residuals, and 85 inputs at the same exact degree.

For the direct equation, the checks establish the exact original and replacement orientation rows; all 14 product and Pell-norm bindings; the source-input map; every unit coefficient and acyclic inverse definition; local polynomial equality of every circuit block; the complete sum-of-squares suffix; all-node liveness; the exact degree upper bound and nonzero leading specialization; and dependence on every declared variable. The retained source pool is expanded independently to authenticate its 25,144-term literal parent residual.

For the native equations, the independent verifier checks 24 display-cut identities per circuit, the full 323-term main norm, the complete 40-term leading forms, all input and coefficient ports, all four fixed coefficient payloads, the closed mask formulas, and 19 retained source records. It certifies the operation counts and the nonzero coefficient witnesses proving degrees 118 and 94.

From the extracted release directory, run
\begin{verbatim}
python3 -B verify.py
\end{verbatim}
The programs use Python 3's standard library. They require no network access. To rebuild the report, run
\begin{verbatim}
python3 -B build_report.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
\end{verbatim}
The exact evaluator accepts a user-supplied tuple; optional modular evaluation is a finite diagnostic. Documentation states the selected equation's domain. Very large exact intermediate values are expected for the high-degree direct equation, so a modular evaluation is the practical first check of an arbitrary tuple.'''
    write('verification.tex',verification.replace('OPS',str(ops)).replace('CONTROL',str(cops)))
    print(json.dumps({'status':'generated','direct_variables':nv,'direct_residuals':nr,'operations':ops,
                      'parent_rows':len(parent['residuals']),'pivots':len(piv),'requests':sum(len(b['requests']) for b in pool['blocks'])},indent=2))

if __name__=='__main__': main()
