#!/usr/bin/env python3
"""Rebuild report inclusions from the packaged, pinned artifacts (stdlib only)."""
from pathlib import Path
import csv
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / 'generated'
OUT.mkdir(exist_ok=True)

def write(name, text):
    (OUT / name).write_text(text, encoding='utf-8')

def tex(s):
    substitutions = {
        '\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
        '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}',
        '~': r'\textasciitilde{}', '^': r'\textasciicircum{}',
        '−': '-', '–': '--', '—': '---', '→': r'$\to$',
        '≤': r'$\le$', '≥': r'$\ge$', '×': r'$\times$',
        '∧': r'$\land$', '↔': r'$\leftrightarrow$', 'Γ': r'$\Gamma$',
    }
    return ''.join(substitutions.get(c, c) for c in s)

write('results_table.tex', (ROOT/'comparison/new_results_table.tex').read_text())
write('census_scope.tex', (ROOT/'comparison/census_scope.tex').read_text())
def break_paths(text):
    return re.sub(r'\\texttt\{([^{}]*(?:/|\\_)[^{}]*)\}',
                  lambda m: r'\nolinkurl{'+m.group(1).replace(r'\_','_')+'}', text)

write('fusion_proof.tex', break_paths((ROOT/'primary/proof/fused_preservation.tex').read_text()))
physical = (ROOT/'companions/proof/symmetric_mf_relative.tex').read_text()
physical = physical.replace(
    r'\section{A relative iPRA proof for the symmetric and fused witness composites}',
    r'\subsection{A relative iPRA proof for the three composites}')
physical = physical.replace(
    r'''\[
 C(88,0)=(0,L,51),\qquad
 C(51,0)=(0,R,122),\qquad
 C(51,1)=(1,R,51),\qquad
 C(88,1)=(1,R,103).
\]''',
    r'''\begin{align*}
 C(88,0)&=(0,L,51), & C(51,0)&=(0,R,122),\\
 C(51,1)&=(1,R,51), & C(88,1)&=(1,R,103).
\end{align*}''')
write('physical_proof.tex', physical)
search = (ROOT/'research/physical/reduction_summary.tex').read_text()
for before, after in [('position$', 'position $'), ('support$', 'support $'),
                      ('path$', 'path $'), ('and$', 'and $'),
                      ('halts,1,208', 'halts, 1,208'),
                      ('is\\texttt', 'is \\texttt')]:
    search = search.replace(before, after)
search = search.replace(
    r'The input revision is \texttt{883da8d55452ea097910ed2509a1eefc833ce292}.',
    'Exact input provenance is recorded in that supplement.')
search = re.sub(r'The\s+input\s+revision\s+is\s*\\texttt\{[0-9a-f]{40}\}\.', 'Exact input provenance is recorded in that supplement.', search)
write('physical_search.tex', break_paths(search))
logical = (ROOT/'primary/proof/logical_search.tex').read_text()
logical = logical.replace(r'\section{Additional logic and grammar searches}', r'\subsection{Logic and grammar searches}')
logical = logical.replace(r'\texttt{research/search/}', r'\file{primary/research/search/}')
logical = logical.replace(r'\begin{tabular}{lrrr}',
    r'\small\setlength{\tabcolsep}{4pt}\begin{tabular}{p{.49\linewidth}rrr}')
logical = logical.replace('Search&Proposals or iterations&Best reader cost&Elapsed seconds',
    r'Search&\shortstack{Proposals or\\iterations}&\shortstack{Best reader\\cost}&\shortstack{Elapsed\\seconds}')
write('logical_search.tex', logical)

write('verification_table.tex', r'''
\begin{longtable}{@{}p{.30\linewidth}p{.23\linewidth}p{.41\linewidth}@{}}
\toprule
Binding or check & Recorded result & What the result supports\\
\midrule\endhead
Exact dense table & 194 controls; 388 rows & Both binary actions exist for
every working state; one distinct terminal label; a checked dense/native
bijection.\\
Independent source graph & 3,695 sites & Every primitive operation,
register argument, branch and resolved destination matches.\\
Complete axiom emitter & 191 atoms & A free-term identity for the entire
emitted stack, including the fused head, both guard failures, the incoming
cache and the fourth field.\\
Arithmetic template binding & 949 instances & Exact composition with the
retained register and duration equations; not a sample of source sites.\\
Literal physical replay & 4,809 outcomes & Arbitrary registers, arbitrary
nonnegative gap, arbitrary nonempty spare list, and both blank exteriors.\\
Independent symbolic work & 1,130,294 steps & Four generic list lemmas
reconstructed from literal rows; largest replay contract 403 steps.\\
Frame and clock closure & 4,808 live endpoints;
one halt & Every live successor has the exact 48-bit padded address;
longest path 38; affine durations positive; halt duration 3.\\
Blank initialization & 57,768 transitions & Whole-tape equality with
source entry 25, native control 84, head $-2$, counter 2 and 26 unit spares.\\
Fusion proof templates & 161 / 205 / 53 lines & Introduction, left
projection and right projection; 419 lines checked again by an independent
checker. The restricted-$\rho$ expansion is an explicit written dependency.\\
Abstract command algebra & 19 symbolic contracts & Selectors, reserved
zero, generalization, and both early-halting MP cases with total projections.\\
Numerical clock regressions & 882 local; 324 composed & Additional
implementation checks; the unbounded duration equations use the written
counter inductions.\\
Physical companion guards & 24,832 windows per table & Exhaustive
radius-three case split for a one-step invariant, followed by QF induction.\\
Structural comparison & 548 old spanning classes & All four new tables
are distinct under the stated broad graph comparison.\\
\bottomrule
\end{longtable}
''')

write('reproduction.tex', r'''
The archive is self-contained for the new constructions and their finite
checks. Python 3.10 or later, with assertions enabled, is sufficient for
the new builders and verifiers. C++ search programs require a C++17
compiler only when rerunning the unsuccessful searches. No network,
external repository checkout, or installed Lean environment is required
for the finite reproduction commands.

From the archive root, run
\begin{verbatim}
python3 -B verify_release.py
python3 -B verify_release.py --full
\end{verbatim}
The default checks the release hashes, all four table conventions and
bindings, symbolic fusion certificates and command identities, and the
independent local companion proof. The full command additionally rebuilds
and replays the principal machine's complete source and physical
certificates and recomputes the corpus comparison. Full replay may take
several minutes. Outputs go into designated replay directories; frozen
inputs are not overwritten. A transcript of the final assembled replay is
included under \file{verification/}.

\begin{longtable}{@{}p{.27\linewidth}p{.67\linewidth}@{}}
\toprule
Directory & Contents\\\midrule\endhead
\file{report/} & This PDF, its main TeX source, generated proof and table
inclusions, and a standard-library input generator.\\
\file{primary/} & Exact FW native and dense tables, source grammar, fold
certificates, constructor, independent verifier, new written proof, and
attributed revised AX11H proof dependencies.\\
\file{companions/} & Three physical variants, literal parent tables,
independent guard/clock checks, relative proof, and the original symmetric
witness archive with its inherited calibration packets.\\
\file{comparison/} & All 104 named-design entries, 106 packet entries,
44 overlapping mechanism classifications, exact source manifests, all
609 spanning 193/194 representatives, seven nonspanning diagnostics, and
an offline comparison checker.\\
\file{research/} & Bounded physical and scanner searches, exact rejected
193-state traces, a second emitter checker, and independent mathematical
audits with explicit limits.\\
\file{verification/} & Final assembled release replay and file-integrity
results. Individual component receipts stay beside their artifacts.\\
\bottomrule
\end{longtable}

To rebuild the PDF from the archive root:
\begin{verbatim}
python3 report/make_inputs.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194_fused_witness.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194_fused_witness.tex
\end{verbatim}
The report requires ordinary LaTeX packages listed in its preamble. Its
transition-table appendix is generated directly from the four delivered
tables, after checking their SHA-256 identities. The named-design appendix
is generated directly from the complete CSV ledger. Original authorship
and licenses are preserved in the component notice files. Reused physical
folds, runtime code, implication derivations, and inherited mathematical
calibration are explicitly attributed; the new contribution is the fused
calculus/interface and the specified new literal implementations.
''')

designs = json.loads((ROOT/'comparison/new_designs4.json').read_text())['new_designs']
parts = []
for design in designs:
    name = design['name']
    source = ROOT/'comparison'/design['table']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == design['dense_sha256']
    rows = {}
    for line in source.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q,b,w,d,n = line.split()
        key = int(q),int(b)
        assert key not in rows
        rows[key] = f'{w}{d}{n}'
    assert set(rows) == {(q,b) for q in range(194) for b in range(2)}
    parts += [r'\clearpage', r'\subsection{'+tex(name)+'}',
              r'\noindent\footnotesize SHA-256: \path{'+design['dense_sha256']+r'}\par',
              r'\begingroup\small\setlength{\tabcolsep}{12pt}',
              r'\begin{longtable}{rll@{\qquad}rll}',
              r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
              r'\midrule\endfirsthead',
              r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
              r'\midrule\endhead', r'\bottomrule\endfoot']
    for q in range(97):
        r = q+97
        parts.append(f'{q} & {rows[q,0]} & {rows[q,1]} & {r} & {rows[r,0]} & {rows[r,1]}' + r'\\')
    parts += [r'\end{longtable}\endgroup']
write('transition_tables.tex', '\n'.join(parts)+'\n')

with (ROOT/'comparison/named_designs104.csv').open(newline='') as f:
    ledger = list(csv.DictReader(f))
assert len(ledger) == len({r['canonical_class'] for r in ledger}) == 104
parts = [r'\clearpage\section{Comparison ledger of the 104 named existing designs}',
         r'''This appendix gives every named existing positive-claim graph in the
source-attributed roster. All identities were freshly bound to the pinned
literal corpus. The first 91 mechanism descriptions are inherited,
attributed classifications from the existing comparison; the 13 newest
entries were classified from their incoming reports. This is a comparison
of reported designs, not 104 independently re-proved absolute calibrations.
Every listed graph has 194 working controls and 194 immediate-action
congruence classes. Full source locations, complete identities, provenance,
and more detailed proof-boundary fields are in
\file{comparison/named_designs104.csv}.''',
         r'\begingroup\footnotesize',
         r'\begin{longtable}{@{}p{.29\linewidth}p{.65\linewidth}@{}}',
         r'\toprule Named design & Mechanism or distinguishing behavior\\',
         r'\midrule\endfirsthead',
         r'\toprule Named design & Mechanism or distinguishing behavior\\',
         r'\midrule\endhead', r'\bottomrule\endfoot']
for row in ledger:
    name = tex(row['name']).replace(r'\_',r'\_\allowbreak ')
    parts.append(r'\texttt{'+name+'} & '+tex(row['mechanism'])+r'\\[3pt]')
parts += [r'\end{longtable}\endgroup']
write('named_ledger.tex','\n'.join(parts)+'\n')
print('Generated report inputs, four exact table listings and the 104-design appendix.')
