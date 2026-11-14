#!/usr/bin/env python3
"""Generate attributed packet/frontier ledgers and the report comparison appendix."""
import collections,csv,hashlib,json,pathlib,re,zipfile
P=pathlib.Path(__file__).resolve().parent
S=P/'source_census'
summary=json.loads((P/'census_summary.json').read_text())
classes=json.loads((P/'literal_classes.json').read_text())
records=json.loads((P/'literal_tables.json').read_text())
byhash={r['sha256']:r for r in records}
byloc={p:r for r in records for p in r['paths']}
frontier=json.loads((S/'frontier194_all.json').read_text())
metadata={}
for f in frontier:
    loc='docs/incoming/pa194_qh5_research_2026-11-14.zip!pa194_qh5_research_2026-11-14/comparison/'+f['representative_file']
    r=byloc[loc]
    k=r['canonical_sha256'] or 'disconnected:'+r['sha256']
    metadata[k]={**f,'evidence_source':'Incoming QH5 comparison/frontier194_all.json; table identity freshly recomputed.'}
new=[
('PA194AX11','1a7defae031c322a5577a3f2cb77d4c3bbc3242c7246f35f073d4dcf12a191d0','Eleven-entry AX interface falls through a full MP field reader; fourth parameter z remains live.','pa194_ax11_research_2026-11-14.zip'),
('PA194QH5','94c85547b3edd0df0a441d45bf22abb52711f2b27cc9e680999232285757dba5','Q premise exchange, no-push visible MP, cache-only Shift and coefficient-five constructors.','pa194_qh5_research_2026-11-14.zip'),
('PA194H5','417e3940a77a6222ccd06885209cc853e572ac48b64acbabf581942f142304c9','Coefficient-five specialization of H; one decoder edge changes all 61 constructor multipliers.','pa194h5_research_2026-11-14.zip'),
('PA194QHS','3bf22abe66e327d63d1feacacda9cc6f1b6529d09ca779c10f22fa5ed3acd103','Q emitter and H no-push controller with symmetric cache-only Shift, deleting a restoration loop.','pa194qhs_conpa_2026-11-14.zip'),
('PA194QN5','30d762c8192a21936511931f35f72888d7b8249128633a5c019435fdd173ad1f','Q emitter, N no-push controller, original sum-one Shift, coefficient-five constructors.','pa194qn_2026-11-14.zip'),
('PA194QN6','72a35e528c1061f61e211d0bcf3a954859d2dbbcfd6b9f7846e4f970bb04e4e9','Q emitter, N no-push controller, original sum-one Shift, coefficient-six constructors; two deliveries duplicate this graph.','pa194qn6_conpa_2026-11-14.zip'),
]
for name,h,mechanism,source in new:
    r=byhash[h];metadata[r['canonical_sha256']]={'name':name,'evidence_status':'supported packet construction','mechanism':mechanism,'evidence_source':'docs/incoming/'+source+' main README and report; table identity freshly recomputed.'}
rows=[]
for r in classes:
    if r['states']!=194:continue
    k=r['canonical_sha256'] or 'disconnected:'+r['sha256'];m=metadata.get(k)
    if m is None and not r['spanning_root']:
        m={'name':'Disconnected search-control fixture','evidence_status':'diagnostic control','mechanism':'Disconnected synthetic table in encoding/contraction research; not a consistency-machine claim.','evidence_source':'Literal file location and lack of any spanning root.'}
    if m is None:m={'name':'Unclassified literal table','evidence_status':'unclassified','mechanism':'No theorem status inferred from graph structure.','evidence_source':'No matched attributed evidence record.'}
    rows.append({**r,**{k:m[k] for k in ('name','evidence_status','mechanism','evidence_source')}})
rows.sort(key=lambda r:(r['evidence_status'],r['name']))
assert not any(r['evidence_status']=='unclassified' for r in rows)
(P/'frontier194.json').write_text(json.dumps(rows,indent=2)+'\n')
def csvout(name,rs,fs):
    with (P/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fs,extrasaction='ignore');w.writeheader();w.writerows(rs)
csvout('frontier194.csv',rows,['name','states','spanning_root','evidence_status','mechanism','canonical_sha256','sha256','sample_path','evidence_source'])
packets=[]
for line in (S/'source_packets_README.md').read_text().splitlines():
    if not line.startswith('| [`'):continue
    c=[x.strip() for x in line.strip('|').split('|')]
    name=re.search(r'\[`([^`]+)`\]',c[0]).group(1)
    packets.append({'directory':name,'location':'Computability/BusyBeaver/Research/PA/docs/'+name,'category':'filed','arrived':c[1],'wrapper':c[2].strip('`'),'reported_contribution':c[3].replace('`',''),'evidence_source':'Pinned PA/docs/README.md packet ledger','sha256':''})
assert len(packets)==61
incoming={
'pa194_ax11_research_2026-11-14.zip':'PA194AX11, using an eleven-entry AX/full-MP-reader interface; also delivers PA194QH5. No verified sub-194 construction.',
'pa194_qh5_research_2026-11-14.zip':'PA194QH5 combines Q, H and coefficient-five arithmetic. Its principal graph duplicates the AX11 packet secondary. Includes an expanded all-table census.',
'pa194h5_research_2026-11-14.zip':'PA194H5 coefficient-five specialization of H; also PA195EvenHX, an even-only candidate scheduler with a parity-prefix proof. No sub-194 machine.',
'pa194qh_conpa_2026-11-13.zip':'PA194QH combines premise-exchanged Q with no-push MP and cache-only Shift. No sub-194 machine.',
'pa194qhs_conpa_2026-11-14.zip':'PA194QHS combines QH with symmetric Shift comparison, removing a restoration loop. No sub-194 machine.',
'pa194qn6_conpa_2026-11-14.zip':'PA194QN6 combines Q, N and coefficient-six arithmetic; retains original sum-one Shift. No sub-194 machine.',
'pa194qn_2026-11-14.zip':'PA194QN5 and PA194QN6, no-push Q/radix compositions. QN6 duplicates the separate QN6 delivery.',
'pa_consistency_reduction_study_2026-11-13.zip':'Comparison; exact direct-selector dual for a fixed primary grammar; primitive factor-three refutation; source-only rotations. No validated reduction.',
'pa_consistency_research_2026-11-14.zip':'New all-offset obstruction for a fixed factor-three codec family; scoped physical and source searches. No validated reduction. Distinct from the older filed packet of the same name.',
'pa_sub194_research.zip':'MP196 detects contradiction immediately after successful MP; 196-state construction and scoped searches. No sub-194 machine.',
'pa_sub194_research_2026-11-13.zip':'A 193-state runtime core passes all source contracts but lacks a valid blank startup; 1,158 elementary startups rejected, plus broader startup theorem and failed reductions.'}
archives=json.loads((P/'archives.json').read_text())
archive_by_path={p:(h,r) for h,r in archives.items() for p in r['paths']}
for name,contribution in incoming.items():
    path='docs/incoming/'+name;h,r=archive_by_path[path]
    packets.append({'directory':name,'location':path,'category':'incoming','arrived':'present at pinned snapshot','wrapper':'see archive manifest','reported_contribution':contribution,'evidence_source':str(S/'incoming_readmes'/(name[:-4]+'.txt')).replace(str(P)+'/', ''),'sha256':h})
(P/'packet_ledger.json').write_text(json.dumps(packets,indent=2)+'\n')
csvout('packet_ledger.csv',packets,['category','directory','location','arrived','reported_contribution','sha256','evidence_source'])
# A strict literal-graph class is distinguished from its evidence label.
counts=collections.Counter(r['evidence_status'] for r in rows if r['spanning_root'])
assert counts=={'supported packet construction':40,'supplementary construction':7,'research auxiliary':25,'research seed':4,'rejected':6},counts
(P/'evidence_summary.json').write_text(json.dumps({'spanning_194_status_counts':dict(counts),'disconnected_194_byte_forms':sum(not r['spanning_root'] for r in rows),'attribution':'Historical evidence labels, not freshly reconstructed proofs of every listed machine.','new_primary_classes_since_76_class_frontier':[x[0] for x in new]},indent=2)+'\n')
def esc(x):
    return ''.join({'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}','\\':r'\textbackslash{}'}.get(c,c) for c in str(x))
def breakname(x):
    return esc(x).replace(r'\_',r'\_\allowbreak{}').replace('-',r'-\allowbreak{}')
c=summary['counts']
tex=r'''\subsection{Frozen inputs and complete scope}
The census is pinned to the commit stated in the main text. It covers all
61 filed delivery directories and all 11 incoming ZIPs, with separate provenance
for the newer incoming packet whose basename repeats an older filed packet.
Every one of the repository catalogue's 535 representative tables was retrieved
at that commit. All 14 literal \texttt{.tm} files outside the filed-documents tree
were also read. The six retained historical ZIP files were expanded recursively;
byte-identical nested archives were read once, while all their outer references
remain in the archive ledger. The indexed catalogue originally deduplicated
7,130 table occurrences to 535 representative graph classes, not 535 proved
consistency machines.

The supplementary JSON pass freshly decoded the 21 repository files identified
as table-bearing by the prior QN JSON census, together with all JSON members
of the incoming and retained historical archives. It examined 1,894 JSON files
and materialized 85 complete transition-table occurrences. It added no new
full graph class to the literal census. The inherited JSON census's wider
8,563-file scan is retained as provenance; it is not presented as a fresh scan
of every repository JSON file. Code-only generators and arbitrary encodings
are outside the automatic recognizer. This explicit boundary prevents a
claim that every conceivable machine hidden in executable text was enumerated.

'''
tex+=f'The resulting frozen comparison contains {c["recognized_table_occurrences"]:,} recognized table occurrences, {c["distinct_table_bytes"]:,} byte forms, and {c["spanning_table_classes"]:,} full spanning graph classes. There are {c["disconnected_byte_forms"]} additional disconnected byte forms, kept separately. Exactly 82 spanning classes have 194 working states. The tables, paths, bytes, hashes, and classifications are included in \\file{{comparison/}}.\n\n'
tex+=r'''\subsection{What graph comparison establishes}
For a proposed root, breadth-first discovery follows the read-zero edge before
the read-one edge and serializes every transition as its write bit, direction,
and discovered successor. A canonical form is considered a full-table form
only when the root reaches every working control. Minimizing over all such
roots removes dependence on state names and on a chosen entry label.
Disconnected tables are not equated merely because they share a large reachable
component. Of the 780 byte forms, 772 have exactly one external terminal label. The other
eight are small or disconnected diagnostic fragments with zero or multiple
exits; missing-row targets are treated as terminal exits in the broad census.
Every one of the 82 spanning 194-state classes has one external halt.
The novelty replay additionally tests every candidate-sized reachable
component of larger tables, so unused extra controls cannot hide an identical
194-state implementation.

PA194TDY has no exact tuple match in the frozen corpus even allowing reflection,
global exchange of the two tape symbols, and deletion of the final halt edge's
write/move distinction. Symbol exchange is a deliberately stronger structural
screen; it is not asserted to preserve a zero-blank computation. Hashes identify
files and comparison results; the equality test uses the complete serialized
transition tuples. This proves relative structural novelty against the stated
inputs. It does not prove a worldwide priority claim or a new logical principle.
The standalone command is
\begin{Verbatim}[fontsize=\small]
python3 comparison/verify_novelty.py
\end{Verbatim}

\subsection{Evidence, aliases, and failed sub-194 proposals}
The 82 spanning 194-state classes consist of 40 principal or supported packet
constructions, seven supplementary constructions, 25 research auxiliaries,
four research seeds, and six rejected tables. These are attributed historical
evidence categories. They are not 82 new proofs reconstructed for this report.
Two further disconnected 194-state byte forms are synthetic search controls.
The full census contains 53 different 193-state spanning graphs, largely
failed startup-repair variants. None is promoted to a blank-start consistency
machine merely because it has the desired number of rows.

The two central sub-194 obstructions are independent. The factor-three formula
codec identifies $E_3(1,0)$ and $I_3(0,1)$ at code 6; the inherited primitive
refutation derives the designated contradiction in 73,393 proof steps. The
separate runtime193 fold preserves its 4,780 source outcomes but breaks blank
initialization. The newer append-zero and relay experiments do not cure that
obstruction. The supplied finite searches and selector dual constrain their
specified transformation families; they are not general lower bounds.

Several names collapse to the same literal graph: repeated PA194C releases,
PA194CSZ/PA194X, PA194QN/PA194NQ, repeated PA194N6 and PA194QNS releases,
and the incoming pairs of QH5 and QN6 deliveries. Conversely, the name
PA194NS denotes both a cache-only guard design (the same graph as HS) and a
different design retaining the sum guard. Names alone are therefore not
usable machine identities. The six classes added after the earlier 76-class
frontier are AX11, QH5, H5, QHS, QN5, and QN6.

The ordinary PA arguments combine numerical-calculus calibration, an all-store
proof-word compiler, fair enumeration of finite command prefixes, source
semantics, and literal-tape realization including blank startup. The repository's
machine-specific iPRA endpoint is a separate unfinished formalization; reported
ordinary PA proofs must not be described as compiled end-to-end Lean/Rocq
or iPRA theorems. Likewise, executable checks of source contracts do not supply
logical consistency calibration by themselves.

\subsection{All delivery packets}
The following ledger covers every delivery at the pinned snapshot. Descriptions
of the 61 filed packets are attributed to their repository ledger; incoming
entries are based on their main reports and READMEs. ``Filed'' and ``incoming''
are locations, not grades of proof. Full unshortened paths and archive hashes
are in \file{comparison/packet_ledger.csv}.
\begingroup\scriptsize
\begin{longtable}{@{}p{0.33\linewidth}p{0.62\linewidth}@{}}
\toprule Packet & Reported contribution \\ \midrule\endhead
'''
for r in packets:
    short=r['directory'].removesuffix('.zip').replace('_2026-11-13','').replace('_2026-11-14','').replace('_2026-10-29','')
    tex+=breakname(short)+r' (\emph{'+r['category']+r'}) & '+esc(r['reported_contribution'])+r' \\'+'\n'
tex+=r'''\bottomrule
\end{longtable}\endgroup

\subsection{Every 194-state full graph class}
The table below contains all 82 spanning classes, including unsuccessful
experiments. ``Supported'' means that the corresponding packet supplies an
ordinary mathematical PA argument and its stated executable evidence;
``supplementary'' is the weaker secondary status attributed by the source
comparison. The detailed CSV includes each full canonical digest and every
source locator. The two disconnected diagnostics are listed in the CSV and
excluded from the 82-class table.
\begingroup\scriptsize
\begin{longtable}{@{}p{0.25\linewidth}p{0.14\linewidth}p{0.54\linewidth}@{}}
\toprule Design & Reported status & Mechanism or limitation \\ \midrule\endhead
'''
status={'supported packet construction':'Supported','supplementary construction':'Supplementary','research auxiliary':'Auxiliary','research seed':'Research seed','rejected':'Rejected'}
for r in rows:
    if r['spanning_root']:tex+=breakname(r['name'])+' & '+status[r['evidence_status']]+' & '+esc(r['mechanism'])+r' \\'+'\n'
tex+=r'''\bottomrule
\end{longtable}\endgroup

\subsection{Larger and diagnostic tables}
The machine-readable census also retains every recognized larger graph,
including alternative 196-state layouts, 197--203-state source realizations,
208-state context/history constructions and their 209--222-state parents or
experiments. In particular, the incoming MP196 immediate-MP-halting construction
and the 195-state even-only scheduler are present: neither meets the requested
strict state bound. The following distribution counts complete spanning graphs,
not established consistency machines. Small diagnostic controls occur alongside
the research machines and are kept visibly separate by their actual state count.
\begin{center}\footnotesize\renewcommand{\arraystretch}{0.85}
\begin{tabular}{rr@{\qquad}rr@{\qquad}rr}
\toprule States & Classes & States & Classes & States & Classes \\ \midrule
'''
items=sorted((int(n),v) for n,v in summary['spanning_classes_by_states'].items())
for i in range(0,len(items),3):
    chunk=items[i:i+3];cells=[f'{n} & {v}' for n,v in chunk]+[' & ']*(3-len(chunk));tex+=' & '.join(cells)+r' \\'+'\n'
tex+=r'''\bottomrule
\end{tabular}\end{center}
'''
(P.parent/'report/comparison_summary.tex').write_text(tex)
print(json.dumps({'packets':len(packets),'spanning_194':sum(r['spanning_root'] for r in rows),'status_counts':dict(counts),'appendix_bytes':len(tex.encode())},indent=2))
