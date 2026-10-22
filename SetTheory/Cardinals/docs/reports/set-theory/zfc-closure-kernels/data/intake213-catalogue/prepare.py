#!/usr/bin/env python3
"""Prepare a bounded catalogue213 successor; apply only after the Write commit."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--apply',action='store_true');a=ap.parse_args();R=a.repo.resolve();O=a.out.resolve();O.mkdir(parents=True,exist_ok=False)
paths=['SetTheory/Cardinals/docs/reports/README.md','SetTheory/Cardinals/docs/reports/manifest.tex'];before={p:(R/p).read_bytes() for p in paths}
for p,b in before.items():(O/('before-'+Path(p).name)).write_bytes(b)
readme=before[paths[0]].decode()
readme+='''\n\n[Supplemental batch 213](set-theory/zfc-closure-kernels/intake-213.md) reconciles\nSources 180–187 from `4b16429bf6`, already placed upstream `d789bf0a28` as part\nof its batch 212. Supplement `0388d93df6` recovers all 788 original members:\n676 immutable Git aliases, 42 delivery aliases, 69 arrival-only members and one\nexact ancillary source. No ZIP was retired twice. The host now has **187 numbered\nsources**, with written coverage of **1–164 and 167–187**; Sources **165–166**\nand the independent batch-209–211 reconciliations remain pending. Category and\ncollection counts remain **290 reports**. Earlier status paragraphs retain their\nhistorical cutoffs.\n\nThe immediate proposals are a broader semantic import cut, a shared implication\nbasis and exact semantic prefix/suffix contracts. The import cut removes\n233,503 bytes from the selected imported source closure, while its seven\nchanged/new Lean files grow by 491 bytes; this is not a repository-wide or\nproof-term reduction. The shared 45-line Lukasiewicz bridge uses a larger core\nand must preserve the maintained two inlinings. Its complete delivered basis\ntotals and the competing independent proof remain separately attributed.\nComplete runtime suffix coverage is still open despite the submitted two-branch\nexample and residual-record counts. The direct full-seed proposal preserves\nliteral named equality and the private-binder freshness argument; it remains\na separate potential simplification. All eight ordinary reviews and their\nlimitations are retained; no supplied program or compiler ran for intake.\n\nSeparate selected phase-twelve checks now pass for the 184-module primary union\n(179 endpoint providers plus five prefix providers), with 15 fresh and 169 reused\nmodules, and for the 67-provider compatibility closure plus two clients. The\nexact import adaptation is locally adopted; its full evidence publication is\nbeing prepared at this catalogue's cutoff. These selected checks do not adopt\nthe other proposals, alter the machine/source program or remove any of the\n4,751 leaves and 6,176 guarded obligations. The written intake preserves the\nbase article and labels; no new internal PA result follows.\n'''
s=before[paths[1]].decode()
a1='179 numbered sources after batch~212. Its written reconciliation covers\nSources~1--164 and~167--179;';b1='187 numbered sources after supplemental batch~213. Its written reconciliation covers\nSources~1--164 and~167--187;';assert s.count(a1)==1;s=s.replace(a1,b1)
a2='{179 numbered sources, with written reconciliations for Sources~1--164 and~167--179;';b2='{187 numbered sources, with written reconciliations for Sources~1--164 and~167--187;';assert s.count(a2)==1;s=s.replace(a2,b2)
mapj=json.loads((R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake213-placement.json').read_bytes())
archive_addition='; supplemental batch~213 (same eight arrivals placed upstream as part of batch~212): '+', '.join(Path(x['archive_path']).name.replace('_',r'\_') for x in mapj['archives'])+r' (\texttt{4b16429bf6})'
ls=s.splitlines();i=next(i for i,x in enumerate(ls) if x.startswith('{article.tex}{batch~143:'));archive_before=ls[i];assert archive_before.endswith('}');ls[i]=archive_before[:-1]+archive_addition+'}';s='\n'.join(ls)+'\n'
key=r'{\raggedright\footnotesize Placements \texttt{b07d1a27b}'
addition=r'''Supplemental batch~213 reconciles Sources~180--187 from \texttt{4b16429bf6}.
Upstream \texttt{d789bf0a28} had already placed these eight packets as part of
its batch~212; supplement \texttt{0388d93df6} adds the exact recovery references
and one otherwise omitted ancillary source. All 788 members remain recoverable:
676 immutable Git aliases, 42 delivery aliases, 69 arrival-only members and one
new file. No ZIP is retired twice. The written host now covers Sources~1--164
and~167--187; Sources~165--166 and the independent batch~209--211 reconciliations
remain pending. The collection still has 290 reports.

Sources~182 and~184 separate semantic model facts from enumerator imports.
The broader cut moves unchanged declarations into small general model modules,
retaining all well-founded-domain assumptions and the compatibility wrappers.
Its selected endpoint projection falls from 192 to 179 modules and removes
233,503 imported source bytes. The seven changed/new Lean files themselves
grow by 491 bytes; these are distinct measures, not a repository-wide or
proof-term reduction. The smaller alternative removes 198,510 selected bytes
and does not stack with the broader extraction. Shared named logic is a
separate maintenance proposal that grows by 1,966 bytes.

Sources~185 and~187 share the dominated implication proof with the unrestricted
calculus by taking the relation to be universally true. Existing composition
and evaluation give exchange in three MP steps; two more MP steps yield S.
No deduction theorem or S premise is assumed. The 45-line Lukasiewicz bridge
in Source~185 is not the complete proof: its delivered core, basis and bridge
total 18,668 bytes, against a raw-predecessor pair of 42,715 bytes. A maintained
adaptation must retain the two checked phase-eleven inlinings, exact numeric
adapter and Tarski tail. The independent 56-step alternative is retained as
another proof, not an additive saving.

Sources~181, 183, 185 and~187 expose semantic coverage with exact entry frames,
full consumed words, arbitrary gaps and valid register lists. Positive complete
edge progress, both decrement branches, increment's spare extension and exact
return frames remain necessary. Source~181 supplies a concrete two-branch CD8
example, not complete coverage. Source~186's supplied residual records retain
all 6,176 guards and 4,751 leaves; their arithmetic is read, not replayed.
Complete suffix contracts remain open. Source~180's fixed-route/clock proposal
must preserve every tape guard and restore all cells before the primitive;
its scheduler duplicate count concerns legacy modules, not the current
primary proof's measured size.

Source~186 also proposes a direct full seed on the original named model.
The existing completeness interface returns satisfaction of the original
formula with literal equality, not merely its equality-erased translation.
Support bounds make the exact private matrix-code binder fresh, while the
upper numerical bundle retains its irreflexivity and coincident-role cases.
This could remove the first indiscernibility quotient, but requires the new
support and named-semantics lemmas before any net saving is established.
The five excluded obligations in Source~183's bounded overapproximation and
Source~187's diagonal-only three-element obstruction retain their limited
scope. No smaller machine, stronger nonhalting statement or internal-PA
endpoint follows from these ordinary reviews.

After the ordinary review cutoff, separate selected phase-twelve import checks
passed for the 184-module primary union (179 endpoint providers plus five
prefix providers): 15 fresh and 169 exactly bound reused modules, followed by
both typed endpoint clients. A separate 67-provider compatibility closure and
two clients also passed. The exact seven Lean files and one producer edit are
locally adopted; full evidence publication is being prepared at this catalogue
cutoff. No supplied archive suite or new Rocq compiler was executed for intake.
These selected checks do not adopt the other proposals or remove any physical
site obligation. The base article and all existing labels are unchanged.

'''
assert s.count(key)==1;s=s.replace(key,addition+key,1)
needle=r'\texttt{7e320f376c}, \texttt{9740f2bd13};';assert s.count(needle)==1;s=s.replace(needle,r'\texttt{7e320f376c}, \texttt{9740f2bd13}, \texttt{d789bf0a28}, \texttt{0388d93df6};')
outputs=dict(zip(paths,[readme.encode(),s.encode()]))
sha=lambda b:hashlib.sha256(b).hexdigest()
record={'status':'CATALOGUE_TEXT_PREPARED','source_count':187,'collection_count':290,'archive_list_exact_append':archive_addition,'placement_list_exact_append':r', \texttt{d789bf0a28}, \texttt{0388d93df6}','files':[]}
for p,b in outputs.items():
 (O/Path(p).name).write_bytes(b);record['files'].append({'path':p,'before_sha256':sha(before[p]),'after_sha256':sha(b)})
if a.apply:
 # Writing follows the separate committed reconciliation, never just the worktree.
 note='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-213.md'
 committed=subprocess.check_output(['git','show','HEAD:'+note],cwd=R);assert committed==(R/note).read_bytes()
 for p,b in outputs.items():assert (R/p).read_bytes()==before[p];(R/p).write_bytes(b)
 record['status']='CATALOGUE_TEXT_APPLIED_AFTER_WRITE_COMMIT';record['write_head']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
(O/'text-control.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
