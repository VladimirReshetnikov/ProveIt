#!/usr/bin/env python3
"""Regenerate the compact report inputs from the comparison ledgers."""
import json, pathlib

HERE=pathlib.Path(__file__).resolve().parent


def esc(value):
    value=str(value).replace("–","-").replace("—","--").replace("≥",">=").replace("≤","<=").replace("→","->")
    mapping={"\\":r"\textbackslash{}","&":r"\&","%":r"\%","$":r"\$","#":r"\#","_":r"\_","{":r"\{","}":r"\}","~":r"\textasciitilde{}","^":r"\textasciicircum{}"}
    return "".join(mapping.get(c,c) for c in value)


rows=json.loads((HERE/"named_designs.json").read_text())
families=json.loads((HERE/"families.json").read_text())
attributed=json.loads((HERE/"sources/attributed_families32.json").read_text())
notes={r["family"]:r for r in attributed}
new_notes={
    "Operand reassociation":("Reassociate operand readers while repairing the shared routine-entry history.","Same resolved primitive graph; 134 physical source addresses move."),
    "MP reader reassociation":("Change the MP operand reader from a balanced tree to a right-associated tree.","Same 3,671 primitive instructions; 87 physical addresses and four native rows change."),
    "Symmetric witness Shift":("Use (1,h) in the cache test and remove cache restoration on the H5X/JH5X sources.","Extra controller absorbed by a context fold: 135+69-10=194; retain the witnessed calculus translation."),
}
family_lines=[r"\begingroup",r"\small",r"\setlength{\tabcolsep}{3pt}",
 r"\begin{longtable}{p{0.20\linewidth}p{0.30\linewidth}p{0.43\linewidth}}",
 r"\caption{All 35 mechanism groups of the 104 named prior 194-state designs. Groups describe mechanisms; they are not counts of proved consistency theorems.}\\",
 r"\toprule Family & Named designs & Common change and proof obligation\\\midrule\endfirsthead",
 r"\toprule Family & Named designs & Common change and proof obligation\\\midrule\endhead",
 r"\bottomrule\endfoot"]
for f in families:
    name=f["family"]
    if name in notes:
        n=notes[name]; description=n["recurring_behavior"]+" "+n["proof_obligation"]
    elif name in new_notes:
        description=" ".join(new_notes[name])
    else:
        description=" ".join(f["mechanisms"][:1])
    family_lines.append(esc(name)+" & "+esc("; ".join(f["named_designs"]))+" & "+esc(description)+r"\\[4pt]")
family_lines += [r"\end{longtable}",r"\endgroup"]
(HERE/"families.tex").write_text("\n".join(family_lines)+"\n")

named_lines=[r"\begingroup",r"\small",r"\setlength{\tabcolsep}{3pt}",
 r"\begin{longtable}{p{0.24\linewidth}p{0.64\linewidth}}",
 r"\caption{All 104 distinct named prior designs. Descriptions are attributed to their packets; complete byte identities, aliases, proof-scope descriptions and current provenance are in the accompanying CSV and JSON ledgers.}\\",
 r"\toprule Design & Mechanism\\\midrule\endfirsthead",
 r"\toprule Design & Mechanism\\\midrule\endhead",r"\bottomrule\endfoot"]
for r in rows:
    named_lines.append(esc(r["name"])+" & "+esc(r["mechanism"])+r"\\[4pt]")
named_lines += [r"\end{longtable}",r"\endgroup"]
(HERE/"named_designs.tex").write_text("\n".join(named_lines)+"\n")

narrative=r'''\subsection{Scope and exact comparison}
The comparison is pinned to ProveIt commit
\texttt{883da8d55452ea097910ed2509a1eefc833ce292}.
The delivered-packet ledger covers all 100 filed PA packets and the six
archives present in \texttt{docs/incoming}: 106 deliveries in total.
Their named roster contains 104 distinct 194-control action graphs.
All 91 literal byte payloads of the inherited named roster were recovered
exactly; the six current incoming packets add thirteen distinct principal
or supplementary designs. The 35 mechanism groups in the family table
are an explanatory taxonomy. They do not assign a common proof status
to every design. Inherited descriptions and calibration claims remain
attributed to the original packets.

The fresh explicit-table scan recognizes 7,907 table occurrences, 1,413
distinct byte payloads and 1,193 whole action-graph classes across all
sizes. In particular, there are 61 classes with 193 working controls,
550 with 194, 31 with 195 and 106 with 196. These figures include rejected
experiments, runtime cores, artificial controls and intermediate parents.
Among the 194-control graphs, 548 have a root from which every working
control is reachable; two are disconnected diagnostics. Counts include
all working controls, exclude terminal labels, and do not extrapolate
finite runs to nonhalting theorems.

The 1,178 directly read Git blobs are bound to the pinned tree by their
Git object identities and additionally by SHA-256. The 75 ZIP references
include repeated payloads at different containment paths. Automatic
recognition covers every tracked \texttt{.tm} file in the two requested
trees and complete numeric five-column text tables in recursively nested
ZIPs. The separate fresh incoming-JSON screen examined 1,379 JSON
occurrences, 1,066 distinct JSON payloads and nine distinct ZIP payloads;
it found no additional complete 193/194-control table in the documented
explicit matrix and record schemas. The scan does not claim to execute
arbitrary generators or recover tables from opaque formats, Lean code,
or TeX prose, nor is it a fresh audit of every standalone JSON file.

\paragraph{Renaming and start states.}
The graph comparison forgets the designated initial control. It preserves
the read symbols, writes and directions, including the actions on entry
to the terminal label. The minimum traversal hash over spanning roots is
an exact invariant under control renaming. For a graph without a spanning
root, such a hash would describe only a reachable part; those buckets
are instead separated by a complete-bijection isomorphism test. This
distinguishes the two disconnected 194-control diagnostics.
Explicit start comments and the dense-zero convention are kept separate.
In particular, densely renumbered native HAZ copies show why dense labels
alone must not be treated as proof of a zero initial control.

\paragraph{Aliases and dependencies.}
Several historical names are aliases: PA194QN and PA194NQ coincide;
multiple PA194C packets repeat one principal graph; PA194QAX11H is the
earlier PA194AX11QH. The name PA194NS has also been used for both a
symmetric sum-guard design and a cached-only design identical to HS.
The ledger therefore binds descriptions to full byte and graph identities,
not to names alone. Later AX11H descendants generally inherit the revised
AX11H written arithmetic calibration while proving new relative source
or physical equivalences. Their mathematical claims and the unfinished
end-to-end Lean endpoint are distinct evidence.

\paragraph{Novelty of the delivered pair.}
PA194OM and PA194OMF are excluded from all prior-corpus counts above.
The self-contained checker compares each with all 550 retained prior
194-control graphs and compares the two new tables with each other.
The comparison allows arbitrary state renaming and root change, global
left/right reflection, global read/write bit exchange, and deletion of
the write/move decorations on terminal-entry edges. Both new tables
remain distinct under this enlarged relation. A large renamed positive
control and the disconnected-diagnostic check also pass.
Bit exchange here strengthens structural comparison; it is not asserted
to preserve blank-zero computation. These finite graph checks establish
novelty within the explicitly pinned corpus, separately from the relative
halting arguments and inherited arithmetic calibration.
'''
(HERE/"comparison_text.tex").write_text(narrative)
print("Generated families.tex, named_designs.tex, comparison_text.tex")
