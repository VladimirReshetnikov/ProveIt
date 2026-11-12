#!/usr/bin/env python3
"""Deterministically render 38/160/4 source TeX; --write only this directory."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,h):
 b=path.read_bytes();assert sha(b)==h,(str(path),sha(b));return b
graw=pin(D/'research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56');g=json.loads(graw)
old=pin(D/'equation.tex','94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635').decode()
constants=r'\textbf{The four fixed integers.}'+old.split(r'\textbf{The four fixed integers.}',1)[1].split(r'\endgroup',1)[0]+r'\endgroup'
assert r'The integer $\mathcal A$ in base 10.' in constants and 'base 61' not in constants.lower()
short=['J','F','alpha','f','i','T','X','Y','r','eta','zeta','y','gamma','square','scale','mainScale','rank','ell','wguard','cube','product','fSquare','cSquare','firstQ','mainQ','vroot','deltaValue','qSquare','productX','scaledIndex','ySquare','qValue','ySum','offset','gammaProduct','timeProduct','rankSeed','rootSkew']
assert len(g['witnesses'])==len(short)==38 and len(set(short))==38 and len(g['source'])==160
inputs=dict(zip(g['witnesses'],short));aliases={row[0]:f'G{i:03d}' for i,row in enumerate(g['source'],1)}
assert len(aliases)==160 and not(set(short)&set(aliases.values()))
ports={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'}
def term(x):
 if type(x)==int:return str(x)
 if x in inputs:return r'\mathtt{'+inputs[x]+'}'
 if x in ports:return ports[x]
 return r'\mathtt{'+aliases[x]+'}'
lines=[r'\noindent $'+term(n)+'='+term(a)+({'*':r'\cdot ', '+':'+', '-':'-'}[o])+term(b)+r'$\par' for n,o,a,b in g['source']]
input_lines=[r'\noindent\texttt{'+', '.join(short[i:i+7])+r'}\par' for i in range(0,len(short),7)]
tex=r'''\documentclass[10pt]{article}
\usepackage[letterpaper,margin=.5in]{geometry}
\usepackage{amsmath,amssymb,multicol}
\pdfinfoomitdate=1\pdftrailerid{}
\pagestyle{empty}\setlength{\parindent}{0pt}\setlength{\parskip}{1pt}
\newcommand{\fl}[1]{\left\lfloor#1\right\rfloor}
\newcommand{\rg}[2]{\{#1,\ldots,#2\}}
\let\bigsum\sum\renewcommand{\sum}{\bigsum\nolimits}
\begin{document}
\begin{center}{\Large A 38-variable quartic equation}\\
Strictly positive integer unknowns; 160 binary-operation abbreviations; exact degree 4.
\end{center}
The 38 unknowns are the following distinct names, each a positive integer:
\par\small
'''+ '\n'.join(input_lines)+r'''
\normalsize
Each monospaced G-name below is an abbreviation, not an additional unknown.
The fixed integers $\beta,K,\mu,\omega$ are defined after the equation.
\begin{multicols}{2}\fontsize{8}{9}\selectfont
% BEGIN GATE GRAPH
'''+ '\n'.join(lines)+r'''
% END GATE GRAPH
\end{multicols}
\noindent The single equation is $\boxed{\mathtt{'''+aliases[g['output']]+r'''}=0}$.
\par\medskip
This is an external source-mapping candidate. Its zero set has been related to
an earlier 40-variable quartic; a Lean proof of the new 38-variable endpoint
has not been completed.
\bigskip
\begin{multicols}{2}\fontsize{7.7}{8.2}\selectfont
'''+constants+r'''
\end{multicols}
\end{document}
'''
report={'scope':'deterministic TeX from pinned 38 graph and exact copied base-10 port recipe; no Lean or PDF-semantics claim',
 'graph_sha256':sha(graw),'inherited_current_page_sha256':sha(old.encode()),'unknowns':short,
 'graph_rows':len(lines),'domain':'positive integers','graph_operations':160,'degree':4,
 'tex_sha256':sha(tex.encode()),'constants_section_sha256':sha(constants.encode())}
if sys.argv==[sys.argv[0],'--write']:
 (P/'equation.tex').write_text(tex);(P/'result.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
elif sys.argv==[sys.argv[0]]:
 assert (P/'equation.tex').read_text()==tex
 assert json.loads((P/'result.json').read_text())==report
else:raise SystemExit('Use no arguments for read-only verification, --write to create candidate files')
print(json.dumps(report,sort_keys=True,indent=2))
