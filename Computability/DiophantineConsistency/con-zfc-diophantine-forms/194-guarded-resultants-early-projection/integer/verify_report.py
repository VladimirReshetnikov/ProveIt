#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent

def source_blocks():
 blocks=[];current=[]
 for line in (ROOT/'PROOF.md').read_text().splitlines():
  if line.startswith('    '):current.append(line[4:])
  elif current:blocks.append('\n'.join(current));current=[]
 if current:blocks.append('\n'.join(current))
 return blocks

def check(s):
 for bad in [r'\emph{',r'\textsuperscript',r'\textsubscript']:
  if bad in s:raise ValueError('unintended raw mathematical markup '+bad)
 if s.count(r'\section{')!=1:raise ValueError('one integration section')
 actual=[b.strip('\n')for b in re.findall(r'\\begin\{verbatim\}\n(.*?)\\end\{verbatim\}',s,re.S)]
 expected=source_blocks()
 if actual!=expected:raise ValueError('literal displayed formulas differ')
 return len(expected)
s=(ROOT/'report_section.tex').read_text();n=check(s);rejected=0
for bad in [s.replace('X^2-16Z^2-8ZF=1','X^2-16Z^2-7ZF=1',1),s.replace('t=4h+2',r't=4h\emph{+2}',1),s.replace(r'\section{',r'\subsection{',1)]:
 try:check(bad)
 except ValueError:rejected+=1
 else:raise ValueError('accepted report corruption')
print(json.dumps({'status':'PASS','literal_displayed_formula_blocks':n,'conversion_corruptions_rejected':rejected,'top_level_sections':1,'unintended_markdown_math_markup':0,'proof_sha256':hashlib.sha256((ROOT/'PROOF.md').read_bytes()).hexdigest(),'section_sha256':hashlib.sha256((ROOT/'report_section.tex').read_bytes()).hexdigest(),'pdf_sha256':hashlib.sha256((ROOT/'report.pdf').read_bytes()).hexdigest()},indent=2,sort_keys=True))
