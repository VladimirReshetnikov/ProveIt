#!/usr/bin/env python3
"""Authenticate the complete factored specifications and export Appendix B."""
from pathlib import Path
import json, tempfile
from polynomial import *
from build_one_square import math_string, export

ROOT=Path(__file__).resolve().parents[1]

def product(ps):
    out=const(1)
    for p in ps:out=mul(out,p)
    return out

def fail_unless(test,msg):
    if not test:raise ValueError(msg)

def authenticate():
    documents=[]
    for n,folder in [(206,'oriented_pool'),(207,'oriented_split')]:
        path=ROOT/'pooling'/folder
        fac=json.loads((path/f'principal{n}_factored.json').read_text())
        full=json.loads((path/f'principal{n}.json').read_text())
        fail_unless(fac['variables']==full['variables'],'factored variable chart differs')
        A=poly(fac['A']);Ts=[];Es=[];bases=[]
        for b in fac['blocks']:
            base=poly(b['base']);bases.append(base)
            T=add(scale(2,mul(A,base)),scale(-1,mul(base,base)),const(-1))
            E={}
            for req in b['requests']:
                m,D,Y,Z=(poly(req[k]) for k in ['m','D','Y','Z'])
                gap=add(m,scale(-1,D))
                E=add(E,mul(gap,gap),scale(-1,mul(Y,Y)),
                      scale(-2,mul(mul(base,Y),add(gap,scale(-1,Z)))))
            fail_unless(T==poly(b['T']) and E==poly(b['E']),'factored block ports differ')
            Ts.append(T);Es.append(E)
        ids=range(3 if fac['split'] else 5)
        R=add(*(mul(mul(bases[j],Es[j]),product([Ts[h] for h in ids if h!=j])) for j in ids),
              scale(-1,mul(var(205),product([Ts[h] for h in ids]))))
        residuals=[poly(r['terms']) for r in fac['quadratic_residuals']]+[R]
        if fac['split']:
            residuals.append(add(mul(Es[3],Ts[4]),mul(Es[4],Ts[3]),
                                scale(-1,mul(var(206),mul(Ts[3],Ts[4])))))
        fail_unless(residuals==[poly(r['terms']) for r in full['residuals']],
                    'factored sum does not equal every full residual')
        documents.append(fac)
    a,b=documents
    fail_unless(a['quadratic_residuals']==b['quadratic_residuals'],'quadratic lists not common')
    fail_unless(a['blocks']==b['blocks'] and a['A']==b['A'],'request tables not common')
    fail_unless(a['variables'][:205]==b['variables'][:205],'shared coordinates differ')
    return a

def main():
    fac=authenticate()
    body=[r'''All coordinates range independently over the integers. These two
polynomials share the following 205 coordinates and 144 quadratic residuals.
Set
\[
A=x_{132}+1,\qquad
(n_0,n_1,n_2,n_3,n_4)=(x_0,x_3,x_{178},x_{95}-1,x_{95}).
\]
For each row of the following table, use the displayed affine polynomials
as $(m,D,Y,Z)$ in its block. The table is part of the polynomial definition;
Pell notation is unnecessary to evaluate it.
\begin{center}\small
\begin{tabular}{@{}crrrrr@{}}\toprule
Block $j$ & Request & $m$ & $D$ & $Y$ & $Z$\\\midrule''']
    for j,block in enumerate(fac['blocks']):
        for i,req in enumerate(block['requests']):
            body.append(str(j)+' & '+str(i)+' & '+' & '.join('$'+math_string(poly(req[k]),True)+'$' for k in ['m','D','Y','Z'])+r'\\')
        if j<4:body.append(r'\addlinespace[3pt]')
    body.append(r'''\bottomrule\end{tabular}\end{center}
Define the following fixed polynomials by finite sums over the table:
\[
T_j=2An_j-n_j^2-1,\qquad
E_j=\sum_{i\in j}\left((m_i-D_i)^2-Y_i^2
                  -2n_jY_i(m_i-D_i-Z_i)\right).
\]
No table entry is an extra unknown. With $Q_0,\ldots,Q_{143}$ given in
full below, the 206-variable equation is
\begin{align*}
P_{206}(x_0,\ldots,x_{205})
&=\sum_{i=0}^{143}Q_i^2+\mathcal R^2=0,\\
\mathcal R
&=\sum_{j=0}^{4}n_jE_j\prod_{\substack{0\le h\le4\\h\ne j}}T_h
  -x_{205}\prod_{h=0}^{4}T_h.
\end{align*}
The 207-variable equation is
\begin{align*}
P_{207}(x_0,\ldots,x_{206})
&=\sum_{i=0}^{143}Q_i^2+\mathcal R_0^2+\mathcal R_1^2=0,\\
\mathcal R_0
&=\sum_{j=0}^{2}n_jE_j\prod_{\substack{0\le h\le2\\h\ne j}}T_h
  -x_{205}T_0T_1T_2,\\
\mathcal R_1&=E_3T_4+E_4T_3-x_{206}T_3T_4.
\end{align*}
These finite formulas, the complete table, and the following list are a
standalone specification of both ordinary integer polynomials. In
particular the symbolic products have the fixed lengths three or five;
there is no variable-length product in a final equation.
''')
    with tempfile.TemporaryDirectory() as td:
        path=Path(td)
        export(dict(variables=fac['variables'][:205],residuals=fac['quadratic_residuals']),path)
        body.append((path/'residuals.tex').read_text().replace('R_{','Q_{'))
    (ROOT/'report/pooling_appendix.tex').write_text('\n'.join(body)+'\n')
    print(json.dumps(dict(status='pass',common_quadratics=144,request_rows=16,
                         complete_factored_profiles=[206,207])))

if __name__=='__main__':main()
