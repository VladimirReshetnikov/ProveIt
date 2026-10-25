#!/usr/bin/env python3
"""Independently reverse presentation-only TeX and compare every proof character."""
from pathlib import Path
import re,json,hashlib,sys
ROOT=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parents[1]
ENTRIES=json.loads((ROOT/'report/PROOF_INPUTS.json').read_text())
def plain_md(s):
 out=[];fenced=False
 for l in s.splitlines():
  if l.startswith('```'): fenced=not fenced;continue
  if not fenced and not l.startswith('    '):
   if re.match(r'^#{1,4}\s+',l):l=re.sub(r'^#{1,4}\s+','',l)
   else:l=re.sub(r'^[-*]\s+','',l)
   l=re.sub(r'`([^`]*)`',r'\1',l)
   l=re.sub(r'\*\*([^*]*)\*\*',r'\1',l)
  out.append(l)
 return re.sub(r'\s+','',re.sub(r'\*\*([^*]*)\*\*',r'\1',''.join(out)))
def plain_tex(s):
 out=[]
 segments=re.split(r'(\\begin\{verbatim\}.*?\\end\{verbatim\})',s,flags=re.S)
 replacements={r'\textbackslash{}':'\\',r'\textasciicircum{}':'^',r'\textasciitilde{}':'~',r'\textless{}':'<',r'\textgreater{}':'>',r'\textasteriskcentered{}':'*'}
 for seg in segments:
  if seg.startswith(r'\begin{verbatim}'):
   out.append(seg.removeprefix(r'\begin{verbatim}').removesuffix(r'\end{verbatim}'));continue
  seg=re.sub(r'^%.*$','',seg,flags=re.M)
  seg=seg.replace(r'\allowbreak{}','')
  # Protect printed braces/backslashes before removing grouping braces.
  seg=seg.replace(r'\{','\x00').replace(r'\}','\x01')
  for a,b in replacements.items():seg=seg.replace(a,'\x02' if b=='\\' else b)
  seg=re.sub(r'\\(?:begin|end)\{(?:itemize|enumerate)\}','',seg)
  seg=re.sub(r'\\item\[(\d+\.)\]',r'\1',seg)
  seg=re.sub(r'\\(?:section|subsection|subsubsection|paragraph|texttt|textbf|item)\b','',seg)
  seg=re.sub(r'\\([_$&#%])',r'\1',seg)
  seg=seg.replace('{','').replace('}','').replace('\x00','{').replace('\x01','}').replace('\x02','\\')
  out.append(seg)
 return re.sub(r'\s+','',''.join(out))
rows=[]
for src,tex in ENTRIES:
 a=ROOT/src;b=ROOT/'report'/tex
 row={'source':src,'tex':'report/'+tex,'source_exists':a.exists(),'tex_exists':b.exists()}
 if a.exists() and b.exists():
  av=plain_md(a.read_text());bv=plain_tex(b.read_text());row.update(source_sha256=hashlib.sha256(a.read_bytes()).hexdigest(),tex_sha256=hashlib.sha256(b.read_bytes()).hexdigest(),presentation_stripped_characters=len(av),exact_character_match=av==bv,source_carets=av.count('^'),tex_carets=bv.count('^'))
  if av!=bv:
   i=next((i for i,(x,y) in enumerate(zip(av,bv)) if x!=y),min(len(av),len(bv)));row.update(first_mismatch=i,source_near=av[max(0,i-50):i+150],tex_near=bv[max(0,i-50):i+150],tex_length=len(bv))
 rows.append(row)
for native_name,native_out in [('proof_body.tex','height_one_full.tex'),('results.tex','height_one_results.tex')]:
 native_source=ROOT/'height_one/report'/native_name
 native_tex=ROOT/'report'/native_out
 if not native_source.is_file():raise ValueError('Missing native height-one proof source '+native_name)
 a=native_source.read_text();b=native_tex.read_text().replace('\\subsection{','\\section{')
 rows.append({'source':'height_one/report/'+native_name,'tex':'report/'+native_out,'source_sha256':hashlib.sha256(native_source.read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256(native_tex.read_bytes()).hexdigest(),'exact_character_match':a==b,'presentation':'Only section nesting changes, independently reversed.'})
result={'status':'PASS' if all(x.get('exact_character_match') for x in rows) else 'FAIL','scope':'Every non-whitespace source character retained after independently stripping Markdown/TeX presentation, including all carets and explicit ordered-list numbers; no producer renderer imported.','proofs':rows}
print(json.dumps(result,indent=2))
if result['status']!='PASS':sys.exit(1)
