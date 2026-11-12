#!/usr/bin/env python3
"""Render the 13/88 graph with the separately reviewed compact-port recipe."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b
raw=pin(D/'research/ordinary13-natural-residue-forced88-degree60/candidate.json','cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2');g=json.loads(raw)
prior=pin(D/'research/ordinary14-natural79-decimal-render-candidate/equation.tex','a9a6ae35d88e3f842d5493fbe6c7f6460285a3d3ae211a40c6b0375ae350ec20').decode()
seed=pin(D/'research/ordinary14-natural79-decimal-render-candidate/DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297').decode().strip()
marker=r'\bigskip\textbf{The four fixed integers.}'
constants=marker+prior.split(marker,1)[1].split(r'\endgroup',1)[0]+r'\endgroup'
assert 'base-10 notation' in constants and 'base 61' not in constants.lower() and len(seed)==15086
names=['argJ','argFuel','argAlpha','argPellF','argIndex','argTime','argW','argScale','argOrdinate','argEta','argZeta','argAuxY','argGamma']
assert len(g['witnesses'])==len(names)==13 and len(set(names))==13 and len(g['source'])==88
ins=dict(zip(g['witnesses'],names));alias={r[0]:f'G{i:03d}' for i,r in enumerate(g['source'],1)}
ports={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'}
def term(x):
 if type(x)==int:return str(x)
 if x in ins:return r'\mathtt{'+ins[x]+'}'
 if x in ports:return ports[x]
 return r'\mathtt{'+alias[x]+'}'
lines=[r'\noindent $'+term(n)+'='+term(a)+({'*':r'\cdot ', '+':'+','-':'-'}[op])+term(b)+r'$\par' for n,op,a,b in g['source']]
inputs=[r'\noindent\texttt{'+', '.join(names[i:i+7])+r'}\par' for i in range(0,len(names),7)]
tex=r'''\documentclass[10pt]{article}
\usepackage[margin=.55in]{geometry}
\usepackage{amsmath,amssymb,multicol}
\pdfinfoomitdate=1\pdftrailerid{}
\pagestyle{empty}\setlength{\parindent}{0pt}
\begin{document}
\begin{center}{\Large A 13-variable natural equation: source-only candidate}\\
Nonnegative integer unknowns; 88 binary-operation abbreviations; exact degree 60 at the fixed ports.
\end{center}
The 13 unknowns below are distinct nonnegative integers:
\par\small
'''+ '\n'.join(inputs)+r'''
\normalsize
Each monospaced G-name below is an abbreviation, not an unknown. The fixed integers $\beta,K,\mu,\omega$ are defined after the equation.
\begin{multicols}{3}\small
% BEGIN GATE GRAPH
'''+ '\n'.join(lines)+r'''
% END GATE GRAPH
\end{multicols}
The single equation is $\boxed{\mathtt{'''+alias[g['output']]+r'''}=0}$.
\par\small The zero-map to the positive parent is an external standard-integer argument; its nonstandard model transfer and iPRA endpoint remain open.

'''+constants+r'''
\par\small The compact fixed-port recipe is distinct from the current-2011 equation. The external parent review is for standard integers and does not establish an iPRA endpoint for this expression.
\end{document}
'''
report={'scope':'compact-port source and separate graph rendering; port recipe binding checked independently, no Lean', 'graph_sha256':hashlib.sha256(raw).hexdigest(),'source_tex_sha256':hashlib.sha256(prior.encode()).hexdigest(),'constant_section_sha256':hashlib.sha256(constants.encode()).hexdigest(),'seed_sha256':hashlib.sha256(seed.encode()).hexdigest(),'seed_digits':len(seed),'input_names':names,'operations':88,'tex_sha256':hashlib.sha256(tex.encode()).hexdigest()}
if sys.argv==[sys.argv[0],'--write']:
 (P/'equation.tex').write_text(tex);(P/'result.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
elif sys.argv==[sys.argv[0]]:
 assert (P/'equation.tex').read_text()==tex and json.loads((P/'result.json').read_text())==report
else:raise SystemExit('use --write or no arguments')
print(json.dumps(report,sort_keys=True,indent=2))
