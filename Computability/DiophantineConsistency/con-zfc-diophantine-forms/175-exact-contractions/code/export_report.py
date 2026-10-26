#!/usr/bin/env python3
"""Render the complete fixed polynomial definition into readable LaTeX."""
from pathlib import Path
import json, re, hashlib
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT/'report'

def variable(i):return 'v_{'+str(i)+'}'

def term_tex(c,indices,first=False):
 sign='-' if c<0 else ('' if first else '+')
 count=Counter(indices)
 factors=[]
 for v,e in sorted(count.items()):
  factors.append(variable(v)+(('^{'+str(e)+'}') if e>1 else ''))
 coeff='' if abs(c)==1 and factors else str(abs(c))
 return sign+coeff+''.join(factors)

def rows_tex(source):
 out=['% Complete literal source rows; generated from source191.json.',
      r'\begingroup\small\setlength{\jot}{3pt}',r'\begin{align*}']
 for number,row in enumerate(source['residuals']):
  pieces=[term_tex(c,m,j==0) for j,(c,m) in enumerate(row['terms'])]
  lines=[];line=''
  # Conservative display width measured in approximate printed characters.
  width=0
  for text,(c,m) in zip(pieces,row['terms']):
   cost=len(str(abs(c)))+sum(5 if j<100 else 6 for j in set(m))+2
   if line and width+cost>79:
    lines.append(line);line='';width=0
   line+=text;width+=cost
  if line:lines.append(line)
  for j,line in enumerate(lines):
   prefix='S_{'+str(number)+r'}={}&' if j==0 else r'&{}'
   out.append(prefix+line+r'\\')
 out.extend([r'\end{align*}',r'\endgroup'])
 return '\n'.join(out)+'\n'

def definition_tex(source,certificate):
 free=certificate['free_source_variables'];retained=certificate['retained_source_rows']
 definitions={s['variable']:s for s in certificate['steps']}
 alive=set(free);ordered=[];pending=set(definitions)
 while pending:
  ready=[v for v in sorted(pending) if {j for _,m in definitions[v]['restoration_source_terms'] for j in m}<=alive]
  if not ready:raise ValueError('cyclic final definition')
  for v in ready:ordered.append(definitions[v]);alive.add(v);pending.remove(v)
 out=[r'\subsection*{Free coordinates and retained residuals}',r'\begin{align*}']
 for name,values in [('F',free),('J',retained)]:
  chunks=[values[i:i+16] for i in range(0,len(values),16)]
  for i,chunk in enumerate(chunks):
   prefix=name+r'={}&(' if i==0 else r'&{}'
   suffix=')' if i==len(chunks)-1 else ','
   out.append(prefix+','.join(map(str,chunk))+suffix+r'\\')
 out.extend([r'\end{align*}',r'\subsection*{The 99 unit definitions in dependency order}',
             r'\begin{longtable}{rrr@{\qquad}rrr@{\qquad}rrr@{\qquad}rrr}',r'\toprule',
             r'$r$&$v$&$\epsilon$&$r$&$v$&$\epsilon$&$r$&$v$&$\epsilon$&$r$&$v$&$\epsilon$\\\midrule\endhead'])
 for i in range(0,len(ordered),4):
  group=ordered[i:i+4];cells=[]
  for s in group:cells.extend([str(s['row']),str(s['variable']),str(s['coefficient'])])
  cells+=['']*(12-len(cells));out.append('&'.join(cells)+r'\\')
 out.extend([r'\bottomrule\end{longtable}'])
 return '\n'.join(out)+'\n'

def main():
 source=json.loads((ROOT/'principal92/sources/source191.json').read_text())
 cert=json.loads((ROOT/'principal92/projection92.json').read_text())
 REPORT.mkdir(exist_ok=True)
 (REPORT/'source191_residuals.tex').write_text(rows_tex(source))
 (REPORT/'factored92_definition.tex').write_text(definition_tex(source,cert))
 profiles=json.loads((ROOT/'PROFILES.json').read_text())
 table=[r'\begin{center}\small',r'\begin{tabular}{rrrrr}',r'\toprule',
        r'Variables&Degree&Residuals&Collected monomials&Exact height\\\midrule']
 for p in profiles:
  m=p['metrics'];terms=m.get('polynomial_terms');height=m.get('polynomial_height')
  table.append('&'.join([str(m['variables_remaining']),str(m['polynomial_degree']),str(m['residuals_remaining']),
                         f'{terms:,}' if terms is not None else 'uncollected',
                         f'{height:,}' if height is not None else 'unmeasured'])+r'\\')
 table.extend([r'\bottomrule\end{tabular}\end{center}'])
 (REPORT/'profiles_table.tex').write_text('\n'.join(table)+'\n')
 text=(ROOT/'compact/section.tex').read_text()
 text=re.sub(r'^\\section\{[^\n]*\}\s*','',text,count=1)
 text=re.sub(r'(?<!\\)\b(qquad|quad)\b',lambda m:'\\'+m.group(1),text)
 text=text.replace(r'\paragraph{Late comparison and attribution.}',r'\subsubsection*{Late comparison and attribution}')
 text+='\n'+(ROOT/'compact/radix47/section.tex').read_text()
 (REPORT/'compact_section.tex').write_text(text)
 # A standalone TeX deliverable contains every finite row and definition.
 body=(REPORT/'report.tex').read_text()
 def expand(m):
  p=REPORT/m.group(1)
  if not p.suffix:p=p.with_suffix('.tex')
  return p.read_text()
 while re.search(r'\\input\{([^}]+)\}',body):body=re.sub(r'\\input\{([^}]+)\}',expand,body)
 (ROOT/'ConZFC_Exact_Contractions.tex').write_text(body)
 receipt={'source191_sha256':hashlib.sha256((ROOT/'principal92/sources/source191.json').read_bytes()).hexdigest(),
          'source_rows':len(source['residuals']),'definitions':len(cert['steps']),
          'free_coordinates':len(cert['free_source_variables']),'retained_rows':len(cert['retained_source_rows']),
          'source_coefficients_rendered':sum(len(r['terms']) for r in source['residuals'])}
 (ROOT/'verification/REPORT_EXPORT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt))

if __name__=='__main__':main()
