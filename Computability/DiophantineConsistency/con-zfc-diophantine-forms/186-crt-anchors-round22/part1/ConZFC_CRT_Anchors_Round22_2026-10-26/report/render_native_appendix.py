#!/usr/bin/env python3
"""Lossless literal-prose rendering of an ASCII mathematical Markdown source.

No Markdown emphasis parsing: unescaped multiplication signs and subscripts
must remain literal rather than disappearing as formatting delimiters.
"""
from pathlib import Path
import argparse,hashlib,json,re
p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=Path(__file__).resolve().parent.parent/'scalar/positive10/native4127/START_ONLY_PROOF.md');p.add_argument('--out',type=Path,default=Path(__file__).with_name('native_appendix.tex'));a=p.parse_args()
def escape(s):
 return ''.join({'\\':r'\textbackslash{}','{':r'\{','}':r'\}','%':r'\%','$':r'\$','&':r'\&','#':r'\#','_':r'\_','^':r'\textasciicircum{}','~':r'\textasciitilde{}'}.get(c,c)for c in s)
def inline(s):
 out=[]
 for k,t in enumerate(re.split('`',s)):
  if k%2:out.append((r'\nolinkurl{'+t+'}')if'/'in t or len(t)>35 else(r'\texttt{'+escape(t)+'}'))
  else:out.append(escape(t))
 return ''.join(out)
lines=a.source.read_text().splitlines();out=[];para=[];code=[]
def flushp():
 if para:out.append(inline(' '.join(para))+'\n');para.clear()
def flushc():
 if code:out.extend([r'\begin{Verbatim}[fontsize=\small,breaklines=true,breakanywhere=true,breaksymbolleft={}]',*code,r'\end{Verbatim}','']);code.clear()
for j,line in enumerate(lines):
 if j==0:
  out += [r'\section{The complete retained Start only native proof}',r'\label{sec:native-source-proof}',
  'This appendix retains the complete incoming ordinary native proof, dated',
  '25 October 2026. Its fifteen-positive P66 equation is an inherited bridge,',
  'not an additional new endpoint. Historical relative paths refer to the',
  'retained native source subtree. The Round22 ten-positive transfer is proved',
  r'in Section~\ref{sec:start4127-positive10}.',''];continue
 if line.startswith('Prepared for Vladimir Reshetnikov'):continue
 if line.startswith('    '):flushp();code.append(line[4:]);continue
 flushc()
 if not line.strip():flushp();continue
 if line.startswith('## '):flushp();out.append(r'\subsection{'+escape(re.sub(r'^\d+\.\s*','',line[3:]))+'}');continue
 if line.startswith('# '):raise ValueError('unexpected second top-level heading')
 para.append(line)
flushc();flushp()
a.out.write_text('\n'.join(out))
print(json.dumps({'source_sha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256(a.out.read_bytes()).hexdigest(),'source_lines':len(lines),'method':'Literal character escaping, no Markdown emphasis parsing; complete source minus duplicate title/date replaced by attribution paragraph'},indent=2))
