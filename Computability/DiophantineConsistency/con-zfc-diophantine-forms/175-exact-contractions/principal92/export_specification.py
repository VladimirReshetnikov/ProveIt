#!/usr/bin/env python3
"""Readable exports of the literal definition, for the containing report."""
from pathlib import Path
from collections import Counter
import json
ROOT=Path(__file__).resolve().parent
def latex_terms(ts):
 out=[]
 for c,mon in ts:
  factors=[]
  for v,power in sorted(Counter(mon).items()):factors.append('y_{'+str(v)+'}'+('^{'+str(power)+'}' if power>1 else ''))
  body=''.join(factors)
  if not body:body=str(abs(c))
  elif abs(c)!=1:body=str(abs(c))+body
  out.append(('-' if c<0 else '+')+body)
 if out and out[0][0]=='+':out[0]=out[0][1:]
 return out or ['0']
def display(lhs,ts):
 tt=latex_terms(ts);lines=[];current=[];length=0
 for term in tt:
  if current and (length+len(term)>105 or len(current)>=4):lines.append(' '.join(current));current=[];length=0
  current.append(term);length+=len(term)
 if current:lines.append(' '.join(current))
 return '\\begin{align*}\n'+lhs+' &={} '+lines[0]+(' \\\\\n'+'\n'.join(' &{} '+line+(' \\\\' if j<len(lines)-2 else '') for j,line in enumerate(lines[1:])) if len(lines)>1 else '')+'\n\\end{align*}\n'
def wrapped_list(name,values,width=16):
 lines=[', '.join(map(str,values[i:i+width])) for i in range(0,len(values),width)]
 return '\\begin{align*}\n'+name+'={}&('+lines[0]+(',' if len(lines)>1 else ')')+' \\\\\n'+'\n'.join(' &'+line+(',' if j<len(lines)-2 else ')')+(' \\\\' if j<len(lines)-2 else '') for j,line in enumerate(lines[1:]))+'\n\\end{align*}\n'
def main():
 source=json.loads((ROOT/'sources/source191.json').read_text());c=json.loads((ROOT/'projection92.json').read_text());v=json.loads((ROOT/'verification.json').read_text());out=ROOT/'specification';out.mkdir(exist_ok=True)
 defs={s['variable']:s['restoration_source_terms'] for s in c['steps']};done=set();order=[]
 def visit(k):
  if k in done:return
  for _,mon in defs[k]:
   for u in mon:
    if u in defs:visit(u)
  done.add(k);order.append(k)
 for k in defs:visit(k)
 (out/'source191_residuals.tex').write_text('% Complete literal source residuals. All indices are zero based.\n'+''.join(display('R_{'+str(i)+'}',r['terms']) for i,r in enumerate(source['residuals'])))
 (out/'definitions92.tex').write_text('% Complete polynomial abbreviations in topological evaluation order.\n'+''.join(display('y_{'+str(k)+'}',defs[k]) for k in order))
 indices=wrapped_list('\\mathcal F',c['free_source_variables'])+wrapped_list('\\mathcal J',c['retained_source_rows'])
 (out/'index_lists.tex').write_text(indices)
 (out/'leading_ray.tex').write_text(wrapped_list('\\boldsymbol a',v['projection191_to92']['leading_witness']['free_coordinate_ray']))
 (out/'free_coordinates.tex').write_text('\\begin{align*}\n'+' \\\\\n'.join(' &'+',\\quad '.join('y_{'+str(c['free_source_variables'][j])+'}=x_{'+str(j)+'}' for j in range(i,min(i+5,92))) for i in range(0,92,5))+'\n\\end{align*}\n')
 text=['P92(x0,...,x91) = sum(R_j(sigma(x))^2 for j in J)', 'All indices are zero based.', 'F = '+str(c['free_source_variables']),'J = '+str(c['retained_source_rows']),'Assign y[F[i]]=x[i]. The following definitions are in topological order:']
 for k in order:text.append('y['+str(k)+'] = '+str(defs[k]))
 text.append('Each [c,[i,...]] denotes c times the product of the indexed y coordinates.')
 for i,r in enumerate(source['residuals']):text.append('R['+str(i)+'] = '+str(r['terms']))
 (out/'complete_specification.txt').write_text('\n'.join(text)+'\n')
 print(json.dumps({'source_residuals':len(source['residuals']),'definitions':len(order),'free_coordinates':len(c['free_source_variables']),'retained_rows':len(c['retained_source_rows'])}))
if __name__=='__main__':main()
