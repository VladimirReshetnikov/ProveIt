"""Convert the audited comparison to a preamble-free LaTeX fragment."""
from pathlib import Path
import re
P=Path(__file__).resolve().parent

def escape(s):
 repl={'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}','\\':r'\textbackslash{}','→':r'$\to$','⊢':r'$\vdash$','≤':r'$\le$','≥':r'$\ge$','–':'--','—':'---','×':r'$\times$'}
 return ''.join(repl.get(c,c)for c in s)
def inline(s):
 out=[];last=0
 for m in re.finditer(r'`([^`]+)`|\*\*([^*]+)\*\*',s):
  out.append(escape(s[last:m.start()]))
  if m[1]:
   if re.search(r'[^ -~]',m[1]):out.append(r'\texttt{'+escape(m[1])+'}')
   else:out.append(r'\nolinkurl{'+m[1]+'}')
  else:out.append(r'\textbf{'+escape(m[2])+'}')
  last=m.end()
 out.append(escape(s[last:]));return ''.join(out)

def main():
 lines=(P/'COMPARISON.md').read_text().splitlines();out=[r'% Requires longtable, booktabs, array, amsmath, and hyperref/xurl.']
 i=0
 while i<len(lines):
  line=lines[i]
  if line.startswith('## Reproduction'):break
  if line.startswith('# '):out.append(r'\section{Comparison of all supplied PA machine designs}');i+=1;continue
  if line.startswith('## '):out.append(r'\subsection{'+inline(line[3:])+'}');i+=1;continue
  if line.startswith('|'):
   table=[]
   while i<len(lines)and lines[i].startswith('|'):
    row=[x.strip()for x in lines[i].strip('|').split('|')]
    if not all(re.fullmatch(r'[:\- ]+',x)for x in row):table.append(row)
    i+=1
   n=len(table[0]);widths={2:[.76,.12],3:[.29,.20,.39],6:[.31,.09,.105,.115,.105,.115]}[n]
   if n==3 and 'Archive' in table[0][0]:widths=[.29,.29,.30]
   out += [r'\begingroup\footnotesize\setlength{\tabcolsep}{3pt}',r'\renewcommand{\arraystretch}{1.14}',r'\begin{longtable}{@{}'+''.join(r'>{\raggedright\arraybackslash}p{'+str(w)+r'\linewidth}'for w in widths)+r'@{}}',r'\toprule']
   header=' & '.join(r'\textbf{'+inline(x)+'}'for x in table[0])+r'\\'
   out += [header,r'\midrule\endfirsthead',r'\toprule',header,r'\midrule\endhead',r'\midrule\multicolumn{'+str(n)+r'}{r}{\emph{Continued on next page}}\\\endfoot',r'\bottomrule\endlastfoot']
   out += [' & '.join(inline(x)for x in row)+r'\\'for row in table[1:]]
   out += [r'\end{longtable}',r'\endgroup'];continue
  if re.match(r'\d+\. ',line):
   out.append(r'\begin{enumerate}')
   while i<len(lines)and (re.match(r'\d+\. ',lines[i])or lines[i].startswith('   ')):
    s=lines[i]
    if re.match(r'\d+\. ',s):out.append(r'\item '+inline(re.sub(r'^\d+\. ','',s)))
    else:out.append(inline(s.strip()))
    i+=1
   out.append(r'\end{enumerate}');continue
  out.append(inline(line));i+=1
 (P/'comparison.tex').write_text('\n'.join(out)+'\n')
 print(P/'comparison.tex')
if __name__=='__main__':main()
