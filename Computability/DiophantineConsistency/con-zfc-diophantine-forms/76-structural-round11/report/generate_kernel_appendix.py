"""Generate exact finite sparse kernels from the delivered data, not a new proof."""
import json
from pathlib import Path
import sympy as s
R=Path(__file__).resolve().parent; P=R.parent/'lucas_h1868';code=json.loads((P/'data/code.json').read_text());kernels=json.loads((P/'data/kernels.json').read_text())
beta,K0,MC,MF=s.symbols('beta K_0 M_C M_F');ports=[beta,K0,MC,MF]
def chunks(a,n):return [a[i:i+n] for i in range(0,len(a),n)]
lines=[r'\section{The exact sparse source kernels}\label{app:kernels}',r'These are the fixed source polynomials used in Section~\ref{sec:lucas}.',r'The four coefficients $\beta,K_0,M_C,M_F$ here are the whole original31',r'tuple in \pathf{lucas_h1868/data/coefficients_binding.json}, not the compact44',r'tuple of the positive equations. Their actual unsigned integer bytes are',r'in the adjacent compressed payloads. Derived signed fixed leaves are',r'in \pathf{lucas_h1868/fixed/}; \pathf{FIXED_COEFFICIENTS.json} specifies',r'the sign-byte convention, exact raw and compressed hashes, and bit lengths.',r'The literal graph also retains the exact integer-polynomial recipes for',r'every derived leaf. No undetermined parameter remains.',r'\paragraph{Weights and target exponents.}',r'The 31 weights, in source variable order, are',r'\[\begin{gathered}']
for i,row in enumerate(chunks(code['weights'],16)):lines.append(','.join(map(str,row))+(r'\\' if i==0 else ''))
lines += [r'\end{gathered}\]',r'The 22 target exponents, in residual order, are',r'\[\begin{gathered}']
for i,row in enumerate(chunks(code['targets_by_row'],11)):lines.append(','.join(map(str,row))+(r'\\' if i==0 else ''))
lines += [r'\end{gathered}\]',r'For each $d=0,1,2$, define $D_d(B)=\sum_e c_{d,e}B^e$ using the',r'following complete lists. A missing exponent has coefficient zero.',r'\begin{longtable}{rrl}',r'\toprule Layer $d$ & Exponent $e$ & Coefficient $c_{d,e}$\\\midrule\endhead']
for layer in kernels['kernels']:
 for term in layer['terms']:
  v=sum(row['coefficient']*s.prod(p**e for p,e in zip(ports,row['powers'])) for row in term['coefficient'])
  lines.append(f"{layer['degree']} & {term['exponent']} & ${s.latex(v)}$\\\\")
lines += [r'\bottomrule\end{longtable}',r'The certified layout has 86 coefficient records sharing 81 stored tap',r'positions, $W=116$, height 1868 and maximum target 1836.',r'Its layer degrees are 1408, 1727 and 1636, with leading coefficients',r'$-6,2,1$. The dominance gaps are 460,25,0 and target headroom is 32.',r'Every coefficient value is retained, so the original bound',r'$2^{2\,134\,927}$ remains valid; the fixed extraction radix satisfies',r'$B_0\ge4096\cdot2^{2\,134\,927}b^2$ whenever the source scale is positive.',r'The separate factored-gap source in \pathf{packing/factor_gap/}',r'reduces 86 weighted records to 85 by an exact positive zero-set bijection.',r'No better completed packing endpoint is claimed for that source, and it',r'is not silently substituted into the recommended equation.']
(R/'kernels.tex').write_text('\n'.join(lines)+'\n')
