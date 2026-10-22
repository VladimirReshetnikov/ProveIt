#!/usr/bin/env python3
"""Own bounded catalogue extension; existing report, counts unchanged."""
from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=Path(__file__).resolve().parent/'catalogue';P.mkdir(exist_ok=False)
paths=['SetTheory/Cardinals/docs/reports/README.md','SetTheory/Cardinals/docs/reports/manifest.tex']
before={x:(R/x).read_text() for x in paths}
for x,s in before.items():(P/Path(x).name).write_text(s)
readme=before[paths[0]]
readme=readme.replace('report; together with batch 208 below, the host has **178 numbered sources**,\nwritten reconciliations for Sources **1–164 and 167–178**, and pending','report; at the batch-208 checkpoint below, the host had **178 numbered sources**,\nwritten reconciliations for Sources **1–164 and 167–178**, and pending',1)
readme+='''

[Batch 212](set-theory/zfc-closure-kernels/intake-212.md) adds Source 179 from
`6f0d42d368`, after placement `9740f2bd13`. The existing host now has
**179 numbered sources**, with written coverage of **1–164 and 167–179**;
Sources **165–166** and the independent reconciliation of the already placed
batch-209–211 proposals remain pending. The collection and category counts
remain **290 reports**. All 862 delivery members remain exactly recoverable:
338 new ancillary files, 462 immutable Git aliases, 24 delivery aliases and
38 arrival-only members, including 32 logs excluded by existing ignore rules.

The submission develops generic affine drain/contraction and literal
source-to-graph proofs, with 1,059 drains and a 367-vertex retained interface
inside the 1,426-vertex graph. Its generated graph/location data are larger;
no smaller binary machine or measured full-build speedup follows. CM215's
six-row transport is prior code; the packet adds integration evidence at its
older pinned snapshot. Ordinary source review found no mathematical defect,
and independent literal readers confirm the graph/rank facts and old430-action
binding. No supplied script or proof compiler was run. Current phase-nine
source/path/zipper-prefix theorems already close two reported decoder gaps;
primitive and return suffix factoring remains open. The rejected214-state
contracts and bounded searches retain their distinct scopes. This reconciliation
preserves the base article and its labels; it does not alter the maintained
Lean/Rocq endpoints or confer a new PA result.
'''
s=before[paths[1]]
s=s.replace('178 numbered sources after batches~205--208. Its written reconciliation covers\nSources~1--164 and~167--178;','179 numbered sources after batch~212. Its written reconciliation covers\nSources~1--164 and~167--179;',1)
s=s.replace('Sources~165--166 still await their written follow-up. Two later\n\\texttt{5314ca0e6b}/\\texttt{b07002a86b} arrivals remain pending.','Sources~165--166 still await their written follow-up. The later batch~212\nreconciles affine-core and CM215 integration evidence without executing supplied\nprograms or compilers. Batches~209--211 have been placed separately; their\nindependent mathematical reconciliation remains pending.',1)
s=s.replace('{178 numbered sources, with written reconciliations for Sources~1--164 and~167--178;','{179 numbered sources, with written reconciliations for Sources~1--164 and~167--179;',1)
lines=s.splitlines();i=next(i for i,l in enumerate(lines) if l.startswith('{article.tex}{batch~143:'))
old_archive=lines[i];assert old_archive.endswith('}')
lines[i]=old_archive[:-1]+r'; batch~212: K215\_Checked\_Affine\_Core\_and\_CM215\_2026-10-21.zip (\texttt{6f0d42d368})}'
s='\n'.join(lines)+'\n'
key=r'{\raggedright\footnotesize Placements \texttt{b07d1a27b}'
pos=s.index(key)
addition=r'''Batch~212 adds Source~179, from \texttt{6f0d42d368}, after placement
\texttt{9740f2bd13}. All 862 members remain recoverable through 338 new files,
462 immutable Git aliases, 24 delivery aliases and 38 arrival-only members;
the latter include 32 raw logs excluded by existing Git ignore rules.
The written reconciliation extends the same report to 179 numbered sources,
with coverage of Sources~1--164 and~167--179. Sources~165--166 and the independent
reconciliation of the separately placed batch~209--211 proposals remain pending.
The collection remains 290 reports.

The new generic drain/contraction argument replaces a total register loop by
its exact affine effect, preserving halting in both directions for arbitrary
natural-valued register files. Literal bindings connect both existing programs
to the same 1,426-vertex graph and its 367-vertex retained interface, after
1,059 drains. The intake's own reader confirms the finite graph/rank facts and
both location domains; it does not replay the 2,852 source-segment obligations.
The delivered 17-module Coq receipt and its 25 closed assumption reports belong
to the auxiliary proof at the stated older snapshot. No new Rocq or Lean
compiler was run. The 284,987-byte generated graph/location data do not establish
a smaller overall proof, faster build or smaller binary machine.

CM215 changes six rows of the existing 215-state table. Its seven implementation
modules are exact prior-code aliases; the packet adds a typed client and
recorded integration evidence. Positive finite simulation blocks and the
marker invariant support the ordinary all-tape transfer; submitted endpoint
receipts remain distinct from a fresh current-provider check. The maintained
phase-nine source binding, routed paths and uniform zipper-entry theorem
already close two decoder gaps named by the report. Primitive and return
suffix contracts still require the full prefix language and arbitrary registers;
the existing 4,751 leaf and 6,176 guarded checks remain.

A rejected 214-state experiment has a positive 1,900-increment sub-contract
but fails a concrete zero-decrement obligation. Of 639 coordinated-provider
variants, 568 have explicit primitive obstructions and 71 only bounded failures.
These results neither refute blank-run calibration by themselves nor prove a
state lower bound. The existing machine, endpoint statements and base-article
labels are unchanged; ordinary source review supplies no new internal-PA result.

'''
s=s[:pos]+addition+s[pos:]
needle=r'\texttt{aecdc78a8b}, \texttt{7e320f376c};'
assert s.count(needle)==1;s=s.replace(needle,r'\texttt{aecdc78a8b}, \texttt{7e320f376c}, \texttt{9740f2bd13};')
for path,text in zip(paths,[readme,s]):(R/path).write_text(text)
sha=lambda b:hashlib.sha256(b).hexdigest()
record={'status':'CATALOGUE_TEXT_READY','files':[{'path':p,'before_sha256':sha(before[p].encode()),'after_sha256':sha((R/p).read_bytes())} for p in paths],
 'archive_list_original_prefix_preserved':(old_archive[:-1] in s),'archive_list_only_addition':r'batch~212: K215\_Checked\_Affine\_Core\_and\_CM215\_2026-10-21.zip (\texttt{6f0d42d368})','placement_list_only_append':'9740f2bd13','source_count':179,'collection_count':290}
assert record['archive_list_original_prefix_preserved']
(P/'text-control.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
