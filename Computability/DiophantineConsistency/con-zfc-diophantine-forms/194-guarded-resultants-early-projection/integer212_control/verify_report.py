#!/usr/bin/env python3
"""Check the previously discovered raw-ASCII mathematical conversion failure."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent

def check(s):
 flat=' '.join(s.split())
 for bad in [r'\textsuperscript',r'\textsubscript',r'\emph{']:
  if bad in s:raise ValueError('unintended mathematical conversion '+bad)
 if s.count(r'\section{')!=1 or s.count(r'\subsection{')!=9:raise ValueError('section structure')
 needles=[r'X\^{}2-(A\^{}2-1)Y\^{}2-1=0',r'S=sum((m\_i-X\_i+Z\_i)\^{}2-Y\_i\^{}2)',r'Y\_(D*l)(A)/D=Y\_l(A) product\_(j=0,\ldots,19) X\_(2\^{}j*l)(A)',r'(X\_(D*l)(A)-1)/D = (D/2)(A\^{}2-1)(Y\_(D*l/2)(A)/(D/2))\^{}2']
 for n in needles:
  if n not in flat:raise ValueError('literal mathematical identity missing '+n)
 return len(needles)
s=(ROOT/'report_section.tex').read_text();n=check(s);rejected=0
for bad in [s.replace(r'X\^{}2-(A\^{}2-1)Y\^{}2-1=0',r'X\textsuperscript{2-(A}2-1)Y\^{}2-1=0'),s.replace('D*l',r'D\emph{l}',1),s.replace(r'Y\_i\^{}2',r'Y\_i2')]:
 try:check(bad)
 except ValueError:rejected+=1
 else:raise ValueError('accepted mathematical rendering corruption')
print(json.dumps({'status':'PASS','literal_key_identities':n,'conversion_corruptions_rejected':rejected,'top_level_sections':1,'subsections':9,'proof_sha256':hashlib.sha256((ROOT/'PROOF.md').read_bytes()).hexdigest(),'section_sha256':hashlib.sha256((ROOT/'report_section.tex').read_bytes()).hexdigest(),'pdf_sha256':hashlib.sha256((ROOT/'report.pdf').read_bytes()).hexdigest()},indent=2,sort_keys=True))
