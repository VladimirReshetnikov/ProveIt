"""Independently parse printed principal TeX residuals back into coefficients."""
from pathlib import Path
import hashlib,json,re,sys
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release')
eqpath=root/'signed/principal215/equation.json'
if not eqpath.is_file():eqpath=root/'signed/package/principal215/equation.json'
texpath=root/'report/residuals.tex';eq=json.loads(eqpath.read_text());tex=texpath.read_text();n=len(eq['variables']);m=len(eq['residuals'])
def need(ok,message):
 if not ok:raise ValueError(message)
need(r'P(x_0,\ldots,x_{%d})=\sum_{i=0}^{%d}R_i(x)^2.'%(n-1,m-1) in tex,'printed polynomial dimension and residual census')
rows=[];current=None
for line in tex.splitlines():
 match=re.fullmatch(r'R_\{(\d+)\}&=(.*)\\\\',line)
 if match:
  need(int(match[1])==len(rows),'printed residual row index')
  rows.append([]);current=rows[-1];expr=match[2]
 elif line.startswith(r'&\quad{}'):
  need(current is not None and line.endswith(r'\\'),'printed continuation')
  expr=line[len(r'&\quad{}'):-2]
 else:continue
 pieces=re.findall(r'[+-]?[^+-]+',expr)
 need(''.join(pieces)==expr,'fully parsed arithmetic expression')
 for piece in pieces:
  sign=-1 if piece.startswith('-') else 1
  body=piece[1:] if piece.startswith(('-','+')) else piece
  lead=re.match(r'\d+',body)
  c=int(lead[0]) if lead else 1
  tail=body[len(lead[0]):] if lead else body
  coords=[];cursor=0
  while cursor<len(tail):
   atom=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',tail[cursor:])
   need(atom is not None,'literal coordinate token')
   i=int(atom[1]);exp=int(atom[2]or'1')
   need(0<=i<n and exp>0,'printed coordinate bound')
   coords.extend([i]*exp);cursor+=len(atom[0])
  need(c>0 and (tail or lead),'literal nonzero coefficient')
  current.append([sign*c,coords])
need(len(rows)==m,'all printed residuals')
need(rows==[r['terms']for r in eq['residuals']],'every printed coefficient and monomial matches JSON')
receipt={'status':'PASS','variables':n,'residuals':m,'literal_terms':sum(map(len,rows)),'equation_sha256':hashlib.sha256(eqpath.read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256(texpath.read_bytes()).hexdigest(),'method':'Parsed printed arithmetic back to integer coefficient/coordinate lists, without renderer imports.'}
binding=root/'report/RESIDUAL_BINDING.json'
if binding.exists():
 b=json.loads(binding.read_text());need(b['source_sha256']==receipt['equation_sha256']and b['tex_sha256']==receipt['tex_sha256'],'appendix declared SHA binding')
print(json.dumps(receipt,indent=2))
