"""Lossless literal proof renderer: mathematical ASCII is never reinterpreted."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
ENTRIES=json.loads((ROOT/'report/PROOF_INPUTS.json').read_text())
# Each input's entire non-whitespace text is retained, with only Markdown presentation changed.
def escape(s):
 mp={'\\':r'\textbackslash{}','{':r'\{','}':r'\}','$':r'\$','&':r'\&','#':r'\#','%':r'\%','_':r'\_\allowbreak{}','^':r'\textasciicircum{}\allowbreak{}','~':r'\textasciitilde{}','<':r'\textless{}\allowbreak{}','>':r'\textgreater{}\allowbreak{}','*':r'\textasteriskcentered{}\allowbreak{}'}
 out=[]
 for c in s:
  out.append(mp.get(c,c))
  if c in '=/+':out.append(r'\allowbreak{}')
 t=''.join(out)
 return re.sub(r'\b[0-9a-f]{40,64}\b',lambda m:r'\allowbreak{}'.join(m.group()[i:i+8] for i in range(0,len(m.group()),8)),t)
def inline(s):
 parts=re.split(r'(`[^`]*`|\*\*[^*]*\*\*)',s)
 return ''.join(r'\texttt{'+escape(p[1:-1])+'}' if p.startswith('`') else r'\textbf{'+escape(p[2:-2])+'}' if p.startswith('**') else escape(p) for p in parts)
def render(text):
 lines=text.splitlines();out=[];i=0
 while i<len(lines):
  line=lines[i]
  if not line.strip():out.append('');i+=1;continue
  if line.startswith(('    ','```','|')):
   fenced=line.startswith('```');table=line.startswith('|');block=[]
   if fenced:i+=1
   while i<len(lines):
    if fenced and lines[i].startswith('```'):i+=1;break
    if not fenced and lines[i] and not lines[i].startswith('|' if table else '    '):break
    block.append(lines[i] if fenced or table else lines[i][4:] if lines[i].startswith('    ') else '');i+=1
   while block and not block[-1].strip():block.pop()
   out.append('\n'.join(['\\begin{verbatim}',*block,'\\end{verbatim}']));continue
  m=re.match(r'^(#{1,4})\s+(.*)',line)
  if m:
   cmd=['section','subsection','subsubsection','paragraph'][min(len(m[1]),4)-1]
   out.append('\\'+cmd+'{'+inline(m[2])+'}');i+=1;continue
  m=re.match(r'^(\d+\.|[-*])\s+(.*)',line)
  if m:
   env='enumerate' if m[1][0].isdigit() else 'itemize';out.append('\\begin{'+env+'}')
   while i<len(lines):
    m=re.match(r'^(\d+\.|[-*])\s+(.*)',lines[i])
    if not m:break
    label=m[1];item=[m[2]];i+=1
    while i<len(lines) and lines[i].strip() and not re.match(r'^(\d+\.|[-*])\s+',lines[i]):item.append(lines[i].strip());i+=1
    out.append('\\item'+('['+label+']' if env=='enumerate' else '')+' '+inline(' '.join(item)))
   out.append('\\end{'+env+'}');continue
  para=[]
  while i<len(lines) and lines[i].strip() and not lines[i].startswith(('    ','#','```','|')):
   para.append(lines[i].strip());i+=1
  out.append(inline(' '.join(para)))
 return re.sub(r'\\allowbreak\{\}(?=\}*[.,;:])','', '\n\n'.join(out)+'\n')
def main():
 entries=list(ENTRIES)
 receipts=[]
 for src,dst in entries:
  text=(ROOT/src).read_text();out='% Complete unabridged proof from '+src+'\n'+render(text)
  (ROOT/'report'/dst).write_text(out)
  receipts.append({'source':src,'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'source_lines':len(text.splitlines()),'source_bytes':len(text.encode()),'tex':'report/'+dst,'tex_sha256':hashlib.sha256(out.encode()).hexdigest(),'complete_literal_render':True})
 (ROOT/'report_audit/PROOF_COVERAGE.json').write_text(json.dumps(receipts,indent=2)+'\n')
 print(json.dumps(receipts,indent=2))
if __name__=='__main__':main()
