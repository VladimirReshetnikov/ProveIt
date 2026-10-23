#!/usr/bin/env python3
"""Build report-layout copies without editing authenticated component sections."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent;out=R/'sections';out.mkdir(exist_ok=True);rows=[]
for name in ['encoding','sun','nine','signed','positive','short','nine_free_adjunct','positive13_adjunct']:
 p=R/name/'section.tex';text=p.read_text();changes=[]
 if name=='sun':
  text=text.replace('eq:split-extraction','eq:sun-split-extraction');changes.append('Namespace local equation label and references to avoid encoding collision.')
 # Only shorten displayed immutable IDs, never mathematical expressions or active data.
 text=text.replace('\\texttt{124c07c0b77a9e20e84676514d8b1ff78536ea3f}','\\texttt{124c07c0b77a}')
 if name=='short':
  start=text.index('\\begin{align*}');end=text.index('\\end{align*}',start)+len('\\end{align*}')
  text=text[:start]+'{\\small\n'+text[start:end]+'\n}'+text[end:];changes.append('Use small font for the first register matrix to fit the main report width.')
 if name=='nine_free_adjunct':
  start=text.index('\\begin{align*}',text.index('The same unconditional'));end=text.index('\\end{align*}',start)+len('\\end{align*}')
  text=text[:start]+'{\\small\n'+text[start:end]+'\n}'+text[end:];changes.append('Small font for long majorant identity block; unchanged mathematical content.')
 q=out/(name+'.tex');q.write_text(text)
 rows.append({'source':str(p.relative_to(R)),'layout_copy':str(q.relative_to(R)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'layout_sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'changes':changes+['Abbreviate displayed source commit to 12 digits; full IDs remain in original sections and ledgers.']})
(R/'SECTION_LAYOUT_MAP.json').write_text(json.dumps(rows,indent=2)+'\n');print('Built eight TeX layout copies; no mathematics changed.')
