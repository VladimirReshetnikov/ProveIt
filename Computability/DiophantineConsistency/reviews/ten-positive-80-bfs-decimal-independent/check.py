#!/usr/bin/env python3
"""Independently compare graph, TeX, PDF, source table and fixed payloads; no Lean execution."""
from pathlib import Path
from hashlib import sha256
import gzip,json,re,subprocess
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ten-positive-80-bfs-decimal-display';G=R/'ten-positive-unshift-t-finite/data/equation_qcube_V2.json';L=R/'ten-positive-80-model-binding-prototype/Direct80Graph.lean';T=R/'direct-bfs-lean-kernel-prototype/DirectBFSSymbolicKernel.lean';S=R/'ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean';C=R/'ten-positive-unshift-t-finite/coefficients'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
g=json.loads(G.read_text());assert g['witnesses']==['J','F','alpha','i','T','w','s','n','eta','zeta'] and g['fixed_numerals']==['beta','K0','MC','MF'] and len(g['source'])==80 and g['output']=='N'
lean=L.read_text().split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\n  ⟨',1)[0]
inputs=re.findall(r'^  let (\w+) : Expr \(Fin 10\) := \.var (\d+)$',lean,re.M);ports=re.findall(r'^  let (\w+) : Expr \(Fin 10\) := \.constant \(p (\d+)\)$',lean,re.M)
assert inputs==[(n,str(i)) for i,n in enumerate(g['witnesses'])] and ports==[(n,str(i)) for i,n in enumerate(g['fixed_numerals'])]
ops=re.findall(r'^  let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)$',lean,re.M);assert len(ops)==80
for (name,op,x,y),(ln,lx,lo,ly) in zip(g['source'],ops):
 alias=lambda z:'4Am1' if z=='fourAm1' else (int(z) if z.isdigit() else z)
 assert (name,op,x,y)==(alias(ln),lo,alias(lx),alias(ly))
assert '⟨Delta,U,Dtau,DpI2,Dg,Q,V,Znum,Mtot,N⟩' in L.read_text()
tex=(P/'equation.tex').read_text();part=tex.split('% BEGIN GRAPH ROWS',1)[1].split('% END GRAPH ROWS',1)[0]
texrows=re.findall(r'\\\(\\mathtt\{(r\d\d)\} = (.*?) ([+\-]|\\cdot) (.*?)\\\)',part);assert len(texrows)==80
raw=subprocess.run(['pdftotext','-layout',str(P/'equation.pdf'),'-'],capture_output=True,text=True,check=True);assert not raw.stderr
pages=raw.stdout.split('\f');assert len(pages)==5 and pages[-1]==''
pdfrows=re.findall(r'\b(r\d\d)\s*=\s*(r\d\d|[a-jβκμν]|\d+)\s*([+−·])\s*(r\d\d|[a-jβκμν]|\d+)',pages[0].replace('µ','μ'));assert len(pdfrows)==80
pdfmap={r:(x,{'+' :'+','−':'-','·':'*'}[op],y) for r,x,op,y in pdfrows};assert len(pdfmap)==80
refs=dict(zip(g['witnesses'],'abcdefghij'));texports={'beta':r'\beta','K0':r'\kappa','MC':r'\mu','MF':r'\nu'};pdfports={'beta':'β','K0':'κ','MC':'μ','MF':'ν'};tr={**refs,**texports};pr={**refs,**pdfports}
for i,(name,op,x,y) in enumerate(g['source'],1):
 reg=f'r{i:02d}';f=lambda v,m:str(v) if isinstance(v,int) else m[v]
 exp=(reg,f(x,tr),r'\cdot' if op=='*' else op,f(y,tr));assert texrows[i-1]==exp
 assert pdfmap[reg]==(f(x,pr),op,f(y,pr))
 tr[name]=r'\mathtt{'+reg+'}';pr[name]=reg
assert 'r80'==pr[g['output']] and r'\boxed{\mathtt{r80}=0}' in tex
assert r'The only unknowns are \(a,b,c,d,e,f,g,h,i,j\in\mathbb Z_{>0}\)' in tex
ref=R/'ten-positive-80-original-kernel-display/equation.tex'
start=r'\textbf{The four fixed integers.}'; end=r'\textbf{Decimal selector list.}'
assert tex.split(start,1)[1].split(end,1)[0]==ref.read_text().split(start,1)[1].split(end,1)[0]
rt=subprocess.run(['pdftotext','-layout',str(ref.with_suffix('.pdf')),'-'],capture_output=True,text=True,check=True);assert not rt.stderr
assert pages[1].replace('µ','μ').split('Decimal selector list.',1)[0]==rt.stdout.split('\f')[1].replace('µ','μ').split('Decimal selector list.',1)[0]
rows_text=T.read_text().split('def rows : List (Nat × Nat × Nat × Nat) := [',1)[1].split(']',1)[0];rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',rows_text)];assert len(rows)==943
import json as _json
assert rows==[tuple(x) for x in _json.loads((R/'indexed-tile-enumeration/TILES.json').read_text())]
selectors=[1+1024*(2**41-(w+256*n+2**17*e+2**25*s+127*2**34)) for w,n,e,s in rows]
texsel=re.findall(r'\d{14}',tex.split('% BEGIN SELECTORS',1)[1].split('% END SELECTORS',1)[0]);pdfsel=re.findall(r'(?<!\d)\d{14}(?!\d)',raw.stdout.split('Decimal selector list.',1)[1]);assert texsel==pdfsel==[f'{x:014d}' for x in selectors]
sl=S.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0];slots=[int(x.strip()) for x in sl.split(',')];ptext=pages[1].replace('µ','μ');printed=[int(x) for x in re.findall(r'\d+',ptext.split('λ = (',1)[1].split(').',1)[0])];assert len(slots)==41 and slots==printed
rho=2**67; beta=rho**8807-1;support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
mc=beta-sum(rho**u for u in support)-2*rho**1063;mf=beta+4+sum(rho**u for u in range(1013,1023))+sum(rho**u for u in range(1065,1074))+rho**2195+rho**3296+(2**51-2)*(rho**4393+rho**5495)+(2**65-1)*sum(rho**u for u in range(8792,8805))+(2**19-1)*rho**8805
K=sum(rho**u for u in (30,62,1100,2201,8849))+sum(a*(rho**(4393-i)+rho**(5495-i)) for i,a in enumerate(selectors))+sum(2**(10+i)*(rho**(4393-x)+rho**(5495-x)) for i,x in enumerate(slots))
for name,value in [('beta',beta),('K',K),('MC',mc),('MF_source',mf)]:
 data=gzip.decompress((C/(name+'.bin.gz')).read_bytes());assert value.to_bytes(len(data),'little')==data
 print('payload',name,'raw_sha256',sha256(data).hexdigest(),'bytes',len(data))
 if name=='K':assert sha256(data).hexdigest()=='0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f'
assert sha(P/'build01/equation.tex')==sha(P/'build02/equation.tex')==sha(P/'equation.tex')=='be7181e835a2b530da007b7b856ea9a799db2f2ad05aef8036a3a95ed21cd849'
assert sha(P/'build01/equation.pdf')==sha(P/'build02/equation.pdf')==sha(P/'equation.pdf')=='412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7'
print('PASS 80 Lean source rows vs JSON (one local identifier rename), graph TeX/PDF rows, 943 selectors, 41 slots, four payloads')
for p in (G,L,P/'equation.tex',P/'equation.pdf',T,S):print('input',p,sha(p))
print('External comparisons only; no Lean file binding, PDF semantics theorem, closed proof ancestry or iPRA replay')
