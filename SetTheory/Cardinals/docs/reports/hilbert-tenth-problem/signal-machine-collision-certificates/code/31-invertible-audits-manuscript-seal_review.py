#!/usr/bin/env python3
"""Seal review findings and hash-bind already inspected artifacts; no science execution."""
from pathlib import Path
import hashlib
import json
import re
R = Path('/workspace/shared/review-report61-manuscript-20261004')
S = Path('/workspace/shared/report61-invertible-returns-release-20261004')
B = Path('/workspace/shared/report61-release-tools-independent-review-20261004/second-build')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
expected_pdf='bb9f61e0620fd23186b351c1427521f83c6eacd90ce18717417235f2fc7d4893'
expected_source='133122c9c7c2c894fdbe30a67d9f5274d9d5293d8bc638a212c9e883181af683'
expected_pins='768309347285fb5c98be4a3a0c691755cb0228b373543beb486f04797ad8f277'
assert digest(B/'Report61.pdf')==expected_pdf
assert digest(S/'Report61.tex')==expected_source
assert digest(S/'manuscript/MANUSCRIPT_PINS.json')==expected_pins
pins=json.loads((S/'manuscript/MANUSCRIPT_PINS.json').read_text())
for name, info in pins.items():
    p=S/'manuscript'/name
    assert p.is_file() and not p.is_symlink()
    assert digest(p)==info['sha256'] and p.stat().st_size==info['bytes']
main=(S/'manuscript/Report61.tex').read_text()
def insert(m):
    name=m.group(1)
    assert name in pins and name!='Report61.tex'
    return (S/'manuscript'/name).read_text()
flat=re.sub(r'\\input\{([^}]+)\}\n',insert,main)
assert flat==(S/'Report61.tex').read_text(), 'Standalone source is not the whole-input-line modular expansion'
for suffix in ['sha256','stat']:
    assert (R/f'frozen_before.{suffix}').read_bytes()==(R/f'frozen_after.{suffix}').read_bytes()
pages=[
'Title, abstract, model and theorem assumptions: all readable and complete.',
'Theorems, determinant product, reversal matrix and GL2 criterion: equations and numbering clean.',
'Contents: section labels and page destinations agree; deliberate contents-page whitespace.',
'Transverse flight lemma and its two-sided inverse proof: all symbols and fractions clean.',
'Translation quotient and corrected n=2/nonzero-scale qualification; gap definition and determinant lemma clean.',
'Adjugate and flux-form proofs, sign telescoping and singular-obstruction opening clean.',
'Affine/projective normalization and start of reversal section: block matrices and Jacobian formula legible.',
'Speed table and seven-rule table complete; labels, signs and speed-ratio columns all legible.',
'Affine-line and event-position tables now adjacent, followed by durations and chamber discussion; former large float gap resolved.',
'Complete endpoint gap table and first-failure proof: rows, signs and prospective times correct and clear.',
'Centered guards and analytic spacetime diagram: exact center times, all seven contacts, stationary markers and unchanged event-4 messenger line verified.',
'Centered inverse, parity, infinite kernel and two-positive-integer-witness corollary/proof: complete and unclipped.',
'Finite-macro clock and positive-compiler theorem: equations and qualification text clean.',
'Positive event count, chronological matrix product, exact guard pullback and interface replacements readable.',
'Literal phase closure, infinite-validity identity and duration inequalities legible; quad typo absent.',
'Zeno scope and rational cyclic-subspace time proof complete; primary-literature discussion begins cleanly.',
'Literature scope, evidence layers and full cone certificate: no missing signs, clipping or misleading provenance.',
'Pinned SHA-256 strings fit; additional-corollary provenance and future-question list readable.',
'No-Zeno-continuation caveat and all four references complete; two logged underfull bibliography lines are visually harmless.'
]
assert len(pages)==19
page_entries=[]
for n,note in enumerate(pages,1):
    p=B/'pages'/f'page-{n:02}.png'
    assert p.is_file()
    page_entries.append({'page':n,'sha256':digest(p),'bytes':p.stat().st_size,'visual_status':'PASS','note':note})
source_bindings={str(S/'manuscript'/name):info for name,info in pins.items()}
source_bindings[str(S/'Report61.tex')]={'sha256':expected_source,'bytes':(S/'Report61.tex').stat().st_size}
bindings={'status':'PASS','date_utc':'2026-10-04','pdf':{'path':str(B/'Report61.pdf'),'sha256':expected_pdf,'pages':19},'manuscript_pins_sha256':expected_pins,'sources':source_bindings,'literal_modular_expansion_equal':True,'all_pages_visually_inspected':True,'pages':page_entries,'frozen_science_preserved':{'sha256':True,'bytes_modes_and_mtime':True},'mathematical_scope':'Conventional mathematical manuscript review with newly authored static rational checks; no formal proof certification, old checker execution or trajectory simulation.'}
(R/'REVIEW_RECEIPT.json').write_text(json.dumps(bindings,indent=2)+'\n')
draft=(R/'REVIEW_DRAFT.md').read_text()
draft=draft.replace('## Status\n\nMathematical source review and fresh static arithmetic complete; final source freeze and PDF all-page inspection pending. This draft is not the final PASS.', '## Verdict\n\n**PASS for the exact final source and 19-page PDF bound below.** All requested mathematical topics and every final rendered page were reviewed. The generic scale-dimension qualification and production issues in the correction log are resolved. No remaining mathematical or visual correction is required. This is conventional review with exact arithmetic support, not proof-assistant certification.')
draft=draft.replace('The proposed addition, separate from the frozen proof, is also checked.', 'The final manuscript addition in Section 5.7, separate from the frozen proof, is also checked.')
draft=draft.replace('The positive-integer input and witness domains must be stated.', 'The final corollary explicitly states the positive-integer input and witness domains.')
draft=draft.replace('Revised float placement and all final pages remain to be checked before PASS.', 'The second build resolves this spacing issue; all 19 final pages were inspected again and pass. Metadata was also directly verified with pdfinfo.')
draft+='\n\n## Final source and PDF binding\n\n'
draft+=f'- Standalone `Report61.tex`: SHA-256 `{expected_source}`\n- Modular manuscript pin file: SHA-256 `{expected_pins}`\n- Final `Report61.pdf`: SHA-256 `{expected_pdf}`; 19 pages, Letter size\n'
draft+='- The standalone TeX is byte-for-byte the expansion of all six pinned modular files, replacing each complete input line, including its terminal newline, by the named module bytes. An initial token-only comparison differed solely by five doubled boundary newlines; the whole-line comparison is exact. Every module byte count and SHA-256 was independently verified. The complete per-file bindings are in `REVIEW_RECEIPT.json`.\n- PDF Title, Author and Subject are populated correctly. Text extraction is available. The final log has no undefined references, missing glyphs, overfull boxes or build errors. Its expected disabled-shell-escape warning and two underfull bibliography lines are harmless and were visually checked.\n- The independent tool reviewer produced the final locked build. This manuscript review does not replace the separate build/release/replay security reviews.\n- Original frozen science hashes, byte sizes, permission modes and modification times match the before/after snapshots. No source science was changed.\n'
draft+='\n## Final all-page visual inspection\n\nThe reviewer opened each native final 120-DPI page image, not merely extracted PDF text. The exact image hashes are recorded in `REVIEW_RECEIPT.json`. All pages pass:\n\n'
for n,note in enumerate(pages,1): draft+=f'{n}. {note}\n'
(R/'REVIEW.md').write_text(draft)
files=['REVIEW.md','REVIEW_RECEIPT.json','review_static_identities.py','static_identity_receipt.json','static_execution.txt','frozen_before.sha256','frozen_after.sha256','frozen_before.stat','frozen_after.stat','seal_review.py']
manifest={'status':'PASS','review_subject_pdf_sha256':expected_pdf,'review_subject_source_sha256':expected_source,'files':{name:{'sha256':digest(R/name),'bytes':(R/name).stat().st_size} for name in files}}
(R/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
with (R/'SHA256SUMS.txt').open('w') as f:
    for name in files+['MANIFEST.json']: f.write(f'{digest(R/name)}  {name}\n')
print(json.dumps({'status':'PASS','review_sha256':digest(R/'REVIEW.md'),'receipt_sha256':digest(R/'REVIEW_RECEIPT.json'),'manifest_sha256':digest(R/'MANIFEST.json'),'pages':19}))
