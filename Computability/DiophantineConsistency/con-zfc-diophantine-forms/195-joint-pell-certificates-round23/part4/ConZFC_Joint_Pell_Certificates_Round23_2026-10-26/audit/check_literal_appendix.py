"""Independently parse both complete printed quartic residual appendices."""
from pathlib import Path
import hashlib,json,re,sys
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release')
def need(q,msg):
 if not q:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(texname,bindingname):
 binding=root/'report'/bindingname;b=json.loads(binding.read_text());texpath=root/'report'/texname;tex=texpath.read_text()
 candidates=[p for p in(root/'signed').rglob('equation.json')if sha(p)==b['source_sha256']];need(candidates,'printed source exacthash absent');eqpath=candidates[0];eq=json.loads(eqpath.read_text());n=len(eq['variables']);m=len(eq['residuals'])
 need(sha(texpath)==b['tex_sha256'],'appendix binding bytes');need(r'P(x_0,\ldots,x_{%d})=\sum_{i=0}^{%d}R_i(x)^2.'%(n-1,m-1)in tex,'printed polynomial dimension/rowcensus')
 need(r'x_0,\ldots,x_{%d}\in\Z'%(n-1)in tex,'printed unrestrictedinteger domain')
 rows=[];current=None
 for line in tex.splitlines():
  match=re.fullmatch(r'R_\{(\d+)\}&=(.*)\\\\',line)
  if match:need(int(match[1])==len(rows),'consecutive printed rowlabel');rows.append([]);current=rows[-1];expr=match[2]
  elif line.startswith(r'&\quad{}'):need(current is not None and line.endswith(r'\\'),'printed continuation');expr=line[len(r'&\quad{}'):-2]
  else:continue
  pieces=re.findall(r'[+-]?[^+-]+',expr);need(''.join(pieces)==expr,'whole expression parsed')
  for piece in pieces:
   sign=-1 if piece.startswith('-')else 1;body=piece[1:]if piece.startswith(('-','+'))else piece;lead=re.match(r'\d+',body);c=int(lead[0])if lead else 1;tail=body[len(lead[0]):]if lead else body;coords=[];cursor=0
   while cursor<len(tail):
    atom=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',tail[cursor:]);need(atom is not None,'literal coordinate syntax');i=int(atom[1]);e=int(atom[2]or'1');need(0<=i<n and e>0,'coordinate bound');coords.extend([i]*e);cursor+=len(atom[0])
   need(c>0 and(tail or lead),'nonzero printed term');current.append([sign*c,coords])
 need(len(rows)==m and rows==[r['terms']for r in eq['residuals']],'all printed monomials and coefficients equalliteral JSON')
 return {'tex':texname,'source':eqpath.relative_to(root).as_posix(),'variables':n,'residuals':m,'literal_terms':sum(map(len,rows)),'source_sha256':sha(eqpath),'tex_sha256':sha(texpath)}
results=[check('residuals.tex','RESIDUAL_BINDING.json'),check('conservative_residuals.tex','CONSERVATIVE_RESIDUAL_BINDING.json')]
print(json.dumps({'status':'PASS','appendices':results,'method':'Complete strict printed-arithmetic parser without renderer imports.'},indent=2))
