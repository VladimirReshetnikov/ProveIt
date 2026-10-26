#!/usr/bin/env python3
"""Generate a complete finite printed definition of the principal equation."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
def monomial(m):
 counts={}
 for v in m:counts[v]=counts.get(v,0)+1
 return ''.join('x_{%d}'%i+('^{%d}'%e if e!=1 else '') for i,e in sorted(counts.items()))
def term(c,m,first=False):
 sign='-' if c<0 else '' if first else '+'
 body=monomial(m);a=abs(c)
 if not body:return sign+str(a)
 return sign+(str(a) if a!=1 else '')+body
def display(name,ts,width=95):
 pieces=[term(c,m,j==0) for j,(c,m) in enumerate(ts)];lines=[];line=''
 for p in pieces:
  if len(line)+len(p)>width and line:lines.append(line);line=''
  line+=p
 lines.append(line or '0')
 out=['\\begin{align*}',name+'&='+lines[0]+('\\\\' if len(lines)>1 else '')]
 out+=['&\\quad '+s+('\\\\' if i+1<len(lines) else '') for i,s in enumerate(lines[1:],1)]
 out+=['\\end{align*}'];return '\n'.join(out)
def main():
 s=json.loads((ROOT/'source206.json').read_text());f=json.loads((ROOT/'factored_pool.json').read_text());g=json.loads((ROOT/'equations/integer84_degree2097808.json').read_text());out=[]
 out.append(r'''\section{Complete finite definition of the 84-variable polynomial}
\label{app:complete84}
This appendix defines the polynomial without a variable exponent or a
coefficient parameter. Begin with formal coordinate symbols
$x_0,\ldots,x_{205}$ and the source residuals below. The symbols eliminated
by the subsequent unit table are polynomial abbreviations, not additional
quantified unknowns. All omitted coefficients are zero.
\subsection{The first 144 residuals}
''')
 for i,r in enumerate(s['residuals'][:-1]):out.append(display('r_{%d}'%i,r['terms']))
 out.append(r'''\subsection{The final residual in factored form}
The following five bases and polynomials define the final residual exactly.
The expanded version supplied in the JSON source has 25,144 monomials; the
factored formula is shorter and equally complete.
''')
 for i,b in enumerate(f['blocks']):
  for field,letter in [('base','n'),('T','T'),('E','E')]:out.append(display(letter+'_{%d}'%i,b[field]))
 out.append(r'''\[
r_{144}=\sum_{i=0}^{4} n_i E_i\prod_{\substack{0\leq j\leq4\\j\ne i}}T_j
-x_{205}\prod_{j=0}^{4}T_j.
\]
\subsection{Acyclic unit definitions}
Each row $(j,v,c)$ in the following table means: remove the term $c x_v$
from the already printed residual $r_j$, multiply what remains by $-c$,
and define $x_v$ to be that polynomial. The coefficient $c$ is always $+1$
or $-1$. Apply the table in its printed order; each defining expression
uses only independent coordinates or earlier definitions. Thus there is
no recursion or implicit equation in the definition.
\begin{longtable}{rrr@{\qquad}rrr}
\toprule
$j$&$v$&$c$&$j$&$v$&$c$\\\midrule\endhead
''')
 triples=[]
 for b in g['blocks']:
  if b['kind']=='definition':
   r,v=b['source_row'],b['source_variable'];c=next(c for c,m in s['residuals'][r]['terms'] if m==[v]);triples.append((r,v,c))
 for at in range(0,len(triples),2):
  row=['%d&%d&%d'%t for t in triples[at:at+2]]
  out.append('&'.join(row)+('&&&' if len(row)==1 else '')+r'\\')
 out.append(r'\bottomrule\end{longtable}')
 chunks=[g['source_input_indices'][i:i+21] for i in range(0,len(g['source_input_indices']),21)]
 out.append('The independent coordinate indices, in the evaluator order, are\n\\begin{gather*}\n'+(',\\\\\n'.join(', '.join(map(str,c)) for c in chunks))+'\n\\end{gather*}\n')
 out.append('Let $J$ be the following set of retained row indices:\n\\begin{gather*}\nJ=\\{'+','.join(map(str,g['retained_source_rows'][:12]))+',\\\\\n'+','.join(map(str,g['retained_source_rows'][12:]))+'\\}.\n\\end{gather*}\nAfter the displayed substitutions, the requested equation is\n\\[ P_{84}=\\sum_{j\\in J}r_j^2=0.\\]\nAll 84 independent coordinates range over $\\mathbb Z$. The graph files give two arithmetic evaluators of this same polynomial; neither graph node adds an unknown.\n')
 (ROOT/'complete_definition.tex').write_text('\n\n'.join(out)+'\n')
 print('wrote',ROOT/'complete_definition.tex',len(triples),'unit definitions')
if __name__=='__main__':main()
