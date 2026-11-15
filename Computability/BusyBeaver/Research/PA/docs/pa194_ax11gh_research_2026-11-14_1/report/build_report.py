#!/usr/bin/env python3
"""Generate the combined TeX report from the delivered proof and data files."""
from pathlib import Path
import json, shutil

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def tex(s):
    replacements={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$',
                  '#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}',
                  '^':r'\textasciicircum{}','≤':r'$\le$','≥':r'$\ge$',
                  '→':r'$\to$','Σ':r'$\Sigma$','₁':r'$_1$','×':r'$\times$',
                  '−':'--','–':'--','—':'---','’':"'",'“':'``','”':"''"}
    return ''.join(replacements.get(c,c) for c in str(s))

def table(path):
    rows={}
    for line in path.read_text().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=(w,d,int(n))
    return rows

def action(a):
    w,d,n=a
    return w+d+('H' if n==194 else str(n))

def make():
    protocol=(ROOT/'proof/new_protocol.tex').read_text()
    preamble=protocol[:protocol.index('\\title{')]
    preamble=preamble.replace('[11pt,a4paper]','[10pt,a4paper]').replace('margin=27mm','margin=24mm')
    preamble+=r'''
\usepackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small PA consistency machines}
\fancyhead[R]{\small New AX11GH / AX11GHS designs}
\fancyfoot[C]{\thepage}
\setlength{\headheight}{14pt}
\setlength{\emergencystretch}{2em}
\hypersetup{pdftitle={Two new 194-state PA consistency designs and exact physical accelerations},pdfauthor={Research contribution for ProveIt},pdfsubject={Full comparison, literal Turing machines, written iPRA proof and reproducible searches}}
\setcounter{tocdepth}{1}
\microtypesetup{expansion=false}
'''
    body=protocol[protocol.index('\\section{Literal'):protocol.index('\\begin{thebibliography}')]
    (HERE/'protocol_body.tex').write_text(body)
    biblio=protocol[protocol.index('\\begin{thebibliography}'):protocol.index('\\end{document}')]
    biblio=biblio.replace('\\end{thebibliography}',r'''
\bibitem{other}
ProveIt, \emph{ZFC research}, \emph{DiophantineConsistency}, and
\emph{ConciseIPRA}, same pinned revision. Their source directories are
\file{Computability/BusyBeaver/Research/ZFC},
\file{Computability/DiophantineConsistency}, and
\file{Logic/PrimitiveRecursiveArithmetic/ConciseIPRA}.
The comparison and provenance data record the exact paths.
\bibitem{reduction}
\emph{PA sub-194 research packet},
\file{Computability/BusyBeaver/Research/PA/docs/pa_sub194_research_2026-11-13}.
The attributed runtime core and local search tools are the bases for the
new bounded searches; they are not a valid 193-state blank-start machine.
\end{thebibliography}''')
    (HERE/'bibliography.tex').write_text(biblio)
    acceleration=(ROOT/'acceleration/acceleration_proof.tex').read_text()
    acceleration=acceleration[acceleration.index('\\section{The two changes}'):acceleration.index('\\end{document}')]
    acceleration=acceleration.replace('\\section{','\\subsection{')
    acceleration='\\section{Exact physical acceleration of both new designs}\n\\label{sec:acceleration}\n'+acceleration
    (HERE/'acceleration_body.tex').write_text(acceleration)
    shutil.copyfile(ROOT/'comparison/family_matrix.tex',HERE/'family_matrix.tex')
    # Dense tables: four parallel blocks, each at most 49 rows.
    out=[r'\section{Complete dense transition tables}',r'\label{app:tables}',
      r'Each row gives the control $q$ and the actions on read symbols 0 and 1. An action $wDq$ writes $w$, moves $D\in\{L,R\}$, and enters $q$. H is the separate halt label 194. All four machines start in control 0 on the all-zero tape. The action printed on a halt transition is retained literally. Native control 194 in the acceleration proof is a working control and is different from dense halt label 194; the bundled label maps specify the conjugacy.']
    families=['PA194AX11GH','PA194AX11GHS','PA194AX11GHF','PA194AX11GHSF']
    for family in families:
        path=ROOT/('acceleration/machines' if family.endswith('F') else 'machines')/family/'machine.tm'
        rows=table(path)
        out += ([r'\clearpage'] if family != families[0] else []) + [r'\subsection{'+family+'}',r'\begingroup\scriptsize',r'\setlength{\tabcolsep}{5pt}',r'\renewcommand{\arraystretch}{1.07}',r'\begin{center}',r'\begin{tabular}{rrr@{\hspace{7mm}}rrr@{\hspace{7mm}}rrr@{\hspace{7mm}}rrr}',r'\toprule',r'$q$ & On 0 & On 1 & $q$ & On 0 & On 1 & $q$ & On 0 & On 1 & $q$ & On 0 & On 1 \\',r'\midrule']
        for i in range(49):
            cells=[]
            for block in range(4):
                q=block*49+i
                cells += [str(q),action(rows[q,0]),action(rows[q,1])] if q<194 else ['','','']
            out.append(' & '.join(cells)+r' \\')
        out += [r'\bottomrule',r'\end{tabular}',r'\end{center}',r'\endgroup',r'\noindent File: \file{'+str(path.relative_to(ROOT))+'}.']
    (HERE/'transition_tables.tex').write_text('\n'.join(out)+'\n')
    # Every named construction is included; hashes and raw paths remain in CSV/JSON.
    names=json.loads((ROOT/'comparison/named_designs.json').read_text())
    out=[r'\clearpage\section{Complete named-design comparison}',r'\label{app:names}',
      r'The following 63 rows are the complete named principal/supplementary roster at the pinned revision. These are attributed design descriptions, not 63 newly checked absolute consistency proofs. The electronic ledger adds graph identities, start provenance, duplicate relations, and packet-specific proof status.',
      r'\begingroup\fontsize{9}{10}\selectfont\begin{longtable}{p{0.22\textwidth}p{0.70\textwidth}}',r'\toprule Name & Distinguishing feature \\ \midrule\endhead']
    for row in sorted(names,key=lambda x:x['name'].casefold()):
        out.append(tex(row['name'])+' & '+tex(row['feature'])+r' \\')
    out += [r'\bottomrule\end{longtable}\endgroup']
    (HERE/'named_ledger.tex').write_text('\n'.join(out)+'\n')
    packets=json.loads((ROOT/'comparison/packet_ledger.json').read_text())
    out=[r'\clearpage\section{Complete delivery ledger}',r'\label{app:packets}',
      r'All 82 filed packets and four current incoming archives are listed below. The contribution column describes the reported contribution of the packet; it is not an endorsement of every historical claim. The full CSV/JSON supplies exact source paths, archive identities, arrival dates, and interpretation. Filed entries are below \file{Computability/BusyBeaver/Research/PA/docs}; incoming entries are below \file{docs/incoming}.',
      r'\begingroup\footnotesize\begin{longtable}{p{0.39\textwidth}p{0.53\textwidth}}',r'\toprule Delivery & Reported contribution \\ \midrule\endhead']
    for row in packets:
        left=r'\path{'+row['delivery']+'}'+r'\newline '+tex(row['location']+'; '+row['arrival'])
        out.append(left+' & '+tex(row['reported_contribution'])+r' \\[2pt]')
    out += [r'\bottomrule\end{longtable}\endgroup']
    (HERE/'packet_ledger.tex').write_text('\n'.join(out)+'\n')
    main=preamble+r'''
\title{Two new 194-state PA consistency designs\\[4pt]
\large Exact physical accelerations, complete corpus comparison,\\
and written weak-arithmetic preservation proofs}
\author{Research contribution for the ProveIt project}
\date{14 November 2026}
\begin{document}
\maketitle
\begin{abstract}
No valid sub-194 machine was obtained. Two new 194-state binary,
single-tape, blank-start designs combine an explicit generalization
binder, a four-operand eleven-entry axiom command, no-push modus
ponens, and a cache-only halt test. Both admit two exact guarded
three-to-one transition shortcuts. All four transition graphs are
distinct from the 110 complete 194-state graph classes found across
86 source deliveries at the pinned repository revision. This report
provides the complete new command/proof argument, literal source
and physical certificates, a uniform iPRA acceleration proof,
and the exact dependency on the latest incoming written PA calibration.
It does not claim a newly completed end-to-end Lean proof.
The unsuccessful reduction searches and their limits are preserved
alongside all tables, code, comparison data, and attributed proof sources.
\end{abstract}
\clearpage
\tableofcontents
\clearpage
\input{overview.tex}
\clearpage
\input{protocol_body.tex}
\clearpage
\input{acceleration_body.tex}
\clearpage
\appendix
\input{transition_tables.tex}
\input{named_ledger.tex}
\input{packet_ledger.tex}
\clearpage
\input{bibliography.tex}
\end{document}
'''
    (HERE/'pa194_ax11gh_research.tex').write_text(main)
    print('Generated combined report, four complete tables, 63-name ledger, and 86-delivery ledger.')

if __name__=='__main__':make()
