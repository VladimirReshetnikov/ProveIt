#!/usr/bin/env python3
"""Check the generated h3/h4 premise exchanges in a separate free-term algebra."""
from pathlib import Path
import json, importlib.util
from itertools import permutations
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('free_term_reference',P.parent/'helpers/free_term_reference.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)

def parse(path):
 it=iter(map(int,path.read_text().split()));n,w,p,r=[next(it)for _ in range(4)]
 fixed=[next(it)for _ in range(n*6+r*5+p*2)]
 def word():return[next(it)for _ in range(next(it))]
 prefix,suffix,g0,g1=[word()for _ in range(4)]
 heads=[[[word()for _ in range(2)]for _ in range(6)]for _ in range(6)]
 assert list(it)==[]
 return(n,w,p,r,fixed,prefix,suffix,g0,g1,heads)

base=parse(P/'input.txt');h3=parse(P/'h3.input.txt');h34=parse(P/'h34.input.txt')
assert base[:-1]==h3[:-1]==h34[:-1]
A,D,H,old,rho=map(v.atom,('A','D','H','old','rho'))
checks=[]
for label,data,flips in [('h3',h3,{2}),('h34',h34,{2,3})]:
 for head in range(6):
  for perm in range(6):
   original=base[-1][head][perm][0]
   expect=original
   if head==2 and head in flips:expect=original[4:10]+original[:4]+original[10:]
   if head==3 and head in flips:expect=original[6:10]+original[:6]+original[10:]
   assert data[-1][head][perm][0]==base[-1][head][perm][0]
   assert data[-1][head][perm][1]==expect
   if head not in flips:continue
   result=v.run(expect,(rho,A,D,H,[old],[]))
   targets=[]
   for a,d,h in permutations((A,D,H)):
    f=v.heads(a,d,h)[head]
    targets.append(v.I(f[2][1],v.I(f[1],f[2][2])))
   assert result[0]in targets
   assert result[1:]==(A,D,H,[old,rho],[])
   checks.append({'input':label,'head':head+1,'parameter_index':perm,'tokens':len(expect),'checked':'antecedents exchanged; old stack and registers preserved'})
print(json.dumps({'status':'PASS','symbolic_head_checks':len(checks),'checks':checks,'scope':'Free-term head semantics only; not a literal-TM source/runtime proof.'},indent=2))
