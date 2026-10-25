#!/usr/bin/env python3
"""Independently parse the literal residual appendix and signed mixed terms."""
from collections import defaultdict
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parent
def require(p,m):
 if not p:raise ValueError(m)
def polynomial(text):
 text=re.sub(r"\\\\(?:\[[^\]]*\]|\*)?","",text)
 text=text.replace(r"&\quad{}","").replace(" ","").replace("\n","")
 if not text.startswith(("+","-")):text="+"+text
 result=defaultdict(int)
 for match in re.finditer(r"([+-])([^+-]+)",text):
  sign,part=match.groups();factors=[];pos=0
  coefficient=re.match(r"\d+",part)
  c=int(coefficient.group()) if coefficient else 1
  if coefficient:pos=coefficient.end()
  while pos<len(part):
   token=re.match(r"x_\{(\d+)\}(?:\^\{(\d+)\})?",part[pos:])
   require(token is not None,"Unexpected TeX polynomial token: "+part[pos:])
   i,k=token.groups();factors.extend([int(i)]*(int(k) if k else 1))
   pos+=token.end()
  result[tuple(sorted(factors))]+=(c if sign=="+" else -c)
 return {m:c for m,c in result.items() if c}
def main():
 text=(ROOT/"ConZFC_Integral_Projection_Lattice.tex").read_text()
 equation=json.loads((ROOT/"gram/balanced/equation.json").read_text())
 start=text.index(r"\begingroup\footnotesize")
 end=text.index(r"\endgroup",start)
 part=text[start:end]
 matches=list(re.finditer(r"r_\{(\d+)\}&=\{\}(.*?)(?=r_\{\d+\}&=|\\end\{align\*\})",part,re.S))
 require([int(m.group(1)) for m in matches]==list(range(177)),"Wrong printed residual census")
 for m,row in zip(matches,equation["residuals"]):
  expected={tuple(indices):c for c,indices in row["terms"]}
  require(polynomial(m.group(2))==expected,"Printed residual mismatch: "+m.group(1))
 stop=text.index(r"\label{eq:edges}")
 begin=text.rfind(r"\begin{align}",0,stop)
 block=text[begin:stop]
 parsed=[]
 for m in re.finditer(r"([+-])\s*r_(?:\{(\d+)\}|(\d+))r_(?:\{(\d+)\}|(\d+))",block):
  s,a,b,c,d=m.groups();i=int(a or b);j=int(c or d)
  parsed.append([min(i,j),max(i,j),1 if s=="+" else -1])
 require(sorted(parsed)==sorted(equation["gram_cross_terms"]),"Printed Gram edge mismatch")
 print(json.dumps({"status":"PASS","parsed_residuals":177,"parsed_mixed_products":13,
                   "method":"Independent TeX token parser compared to literal JSON"}))
if __name__=="__main__":main()
