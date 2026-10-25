from pathlib import Path
root=Path(__file__).resolve().parent
lines=(root/'PROOF.md').read_text().splitlines()
def esc(t):
 t=t.replace('**','')
 return ''.join({'\\':r'\textbackslash{}','_':r'\_','%':r'\%','&':r'\&','#':r'\#','$':r'\$','{':r'\{','}':r'\}','^':r'\textasciicircum{}','~':r'\textasciitilde{}'}.get(c,c) for c in t)
out=['% Complete full proof; generated without omitting sections.'];incode=False
for line in lines:
 if line.startswith('    '):
  if not incode:out.extend([r'\begingroup\small',r'\begin{verbatim}']);incode=True
  out.append(line[4:]);continue
 if incode:out.extend([r'\end{verbatim}',r'\endgroup']);incode=False
 if line.startswith('# '):out.append(r'\section{'+esc(line[2:])+'}')
 elif line.startswith('## '):out.append(r'\subsection{'+esc(line[3:])+'}')
 else:out.append(esc(line))
if incode:out.extend([r'\end{verbatim}',r'\endgroup'])
(root/'section.tex').write_text('\n'.join(out)+'\n')
