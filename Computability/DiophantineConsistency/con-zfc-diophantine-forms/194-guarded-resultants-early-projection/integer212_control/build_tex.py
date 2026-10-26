#!/usr/bin/env python3
"""Optional document regeneration using Pandoc; literal mathematical operators preserved."""
from pathlib import Path
import re,subprocess,tempfile
ROOT=Path(__file__).resolve().parent
s=(ROOT/'PROOF.md').read_text().replace('justified in Section 3','justified by the scaled-cap argument below');lines=[]
for line in s.splitlines():
 if line.startswith('## '):line=re.sub(r'^## [0-9]+\. ','## ',line)
 if not line.startswith('    '):
  parts=line.split('`')
  for i in range(0,len(parts),2):parts[i]=parts[i].replace('*',r'\*').replace('_',r'\_')
  line='`'.join(parts)
 lines.append(line)
with tempfile.TemporaryDirectory(prefix='integer212-tex-')as td:
 p=Path(td)/'proof.md';p.write_text('\n'.join(lines)+'\n')
 subprocess.run(['pandoc',str(p),'-f','markdown-superscript-subscript','-t','latex','--top-level-division=section','-o',str(ROOT/'report_section.tex')],check=True)
out=(ROOT/'report_section.tex').read_text()
if any(bad in out for bad in ['\\textsuperscript','\\textsubscript','\\emph{']):raise ValueError('unintended Markdown math conversion')
if out.count('\\section{')!=1:raise ValueError('one top-level integration section required')
