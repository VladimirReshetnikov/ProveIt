#!/usr/bin/env python3
"""Independent finite re-evaluation of the pinned trace75 decimal display."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import gzip,json,re,subprocess,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];H=D/'research/trace75-bfs-decimal-display';G=D/'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json';B=D/'research/direct-bfs-lean-kernel-prototype/DirectBFSSymbolicKernel.lean';T=D/'research/indexed-tile-enumeration/TILES.json';S=D/'research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean';REF=D/'research/ten-positive-80-bfs-decimal-display/equation.tex';RPDF=REF.with_suffix('.pdf');PDF=H/'equation.pdf';TEX=H/'equation.tex'
pins={G:'8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',B:'8a1cd03117bae77e3ed13a853f5bff658ba3acf6ef7dd77bff520cd5cc7f1129',T:'f06d1b9858281f1adcbc431d3c0df9b07df1a231793629650b2d3c09eac56549',S:'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',PDF:'86ad6a7ca7e7125818ff08014cb03c04540bb531b072a75cfa02ae29b0e8edd6',TEX:'98994625e4b56ce927b3c8792ce2411e83cc4df254a8ec8ee9652ddaf710d388',REF:'be7181e835a2b530da007b7b856ea9a799db2f2ad05aef8036a3a95ed21cd849',RPDF:'412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7'}
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():assert sha(p)==h,(str(p),'pin')
g=json.loads(G.read_text());assert len(g['source'])==g['operations']==75 and len(g['witnesses'])==10
# Independently parse the two retained selector-table representations.
s=B.read_text().split('def rows : List (Nat × Nat × Nat × Nat) := [\n',1)[1].split('  ]\n',1)[0];lean_rows=[tuple(map(int,x)) for x in re.findall(r'  \((\d+), (\d+), (\d+), (\d+)\),',s)];json_rows=[tuple(x) for x in json.loads(T.read_text())];assert lean_rows==json_rows and len(json_rows)==943
slots=[int(x.strip()) for x in S.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0].split(',')];assert len(slots)==41
rho=1<<67;beta=rho**8807-1
selectors=[1+1024*(2**41-(w+256*n+2**17*p+2**25*s+127*2**34)) for w,n,p,s in json_rows]
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
mc=beta-sum(rho**u for u in support)-2*rho**1063
mf=beta+4+sum(rho**u for u in range(1013,1023))+sum(rho**u for u in range(1065,1074))+rho**2195+rho**3296+(2**51-2)*(rho**4393+rho**5495)+(2**65-1)*sum(rho**u for u in range(8792,8805))+(2**19-1)*rho**8805
kernel=rho**30+rho**62+rho**1100+rho**2201+rho**8849+sum(v*(rho**(4393-u)+rho**(5495-u)) for u,v in enumerate(selectors))+sum(2**(10+u)*(rho**(4393-v)+rho**(5495-v)) for u,v in enumerate(slots))
values={'beta':beta,'K0':kernel,'MC':mc,'MF':mf};rawhash={};C=D/'research/ten-positive-unshift-t-finite/coefficients'
for n,v in values.items():
 meta=g['coefficient_binding']['ports'][n];p=C/meta['file'];z=p.read_bytes();raw=gzip.decompress(z);assert sha256(z).hexdigest()==meta['parent_gzip_sha256'] and sha256(raw).hexdigest()==meta['raw_sha256'] and v.to_bytes(len(raw),'little')==raw;rawhash[n]=sha256(raw).hexdigest()
# Compare both the literal TeX gate lines and PDF text extraction to JSON.
t=TEX.read_text();section=t.split('% BEGIN GRAPH ROWS',1)[1].split('% END GRAPH ROWS',1)[0];lines=[x for x in section.splitlines() if x.startswith('\\(\\mathtt{r')];assert len(lines)==75
refs=dict(zip(g['witnesses'],list('abcdefghij')));refs.update({'beta':'\\beta','K0':'\\kappa','MC':'\\mu','MF':'\\nu'})
for i,(name,op,a,b) in enumerate(g['source'],1):
 def tok(x):return str(x) if type(x) is int else refs[x]
 expected='\\(\\mathtt{r%02d} = %s %s %s\\)\\\\'%(i,tok(a),'\\cdot' if op=='*' else op,tok(b));assert lines[i-1]==expected,(i,lines[i-1],expected);refs[name]='\\mathtt{r%02d}'%i
assert refs[g['output']]=='\\mathtt{r75}'
def textpdf(p):return subprocess.run(['pdftotext','-layout',str(p),'-'],check=True,capture_output=True,text=True).stdout.replace('µ','μ')
txt=textpdf(PDF);pages=txt.split('\f');assert len(pages)==5 and pages[-1]==''
pat=r'\b(r\d{2})\s*=\s*(r\d{2}|[a-jβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-jβκμν]|\d+)';got=re.findall(pat,pages[0]);assert len(got)==75
refs=dict(zip(g['witnesses'],list('abcdefghij')));refs.update({'beta':'β','K0':'κ','MC':'μ','MF':'ν'});rows={n:(a,op,b) for n,a,op,b in got};assert len(rows)==75
for i,(name,op,a,b) in enumerate(g['source'],1):
 def tok(x):return str(x) if type(x) is int else refs[x]
 key='r%02d'%i;assert rows[key]==(tok(a),{'+':'+','-':'−','*':'·'}[op],tok(b));refs[name]=key
assert 'The equation is r75 = 0' in ' '.join(pages[0].split())
printed=re.findall(r'(?<!\d)\d{14}(?!\d)',txt.split('Decimal selector list.',1)[1]);assert printed==[f'{x:014d}' for x in selectors]
printed_slots=[int(x) for x in re.findall(r'\d+',pages[1].split('λ = (',1)[1].split(').',1)[0])];assert printed_slots==slots
start=r'\textbf{The four fixed integers.}';end=r'\textbf{Decimal selector list.}';assert t.split(start,1)[1].split(end,1)[0]==REF.read_text().split(start,1)[1].split(end,1)[0];assert pages[1].split('Decimal selector list.',1)[0]==textpdf(RPDF).split('\f')[1].split('Decimal selector list.',1)[0]
# Independently evaluate all coefficients of the univariate ray modulo p.
P=1000000007;state={n:[0,1] for n in g['witnesses']};state.update({n:[v%P] for n,v in values.items()})
def value(x):return [x%P] if type(x) is int else state[x]
for name,op,a,b in g['source']:
 x,y=value(a),value(b)
 if op=='*':
  z=[0]*(len(x)+len(y)-1)
  for i,u in enumerate(x):
   for j,v in enumerate(y):z[i+j]=(z[i+j]+u*v)%P
 else:
  z=[0]*max(len(x),len(y))
  for i,u in enumerate(x):z[i]=(z[i]+u)%P
  for i,v in enumerate(y):z[i]=(z[i]+(v if op=='+' else -v))%P
 state[name]=z
z=state[g['output']];assert len(z)-1==402 and z[402]==607287076
degree={n:1 for n in g['witnesses']};degree.update({n:0 for n in g['fixed_numerals']})
for name,op,a,b in g['source']:
 da=0 if type(a) is int else degree[a];db=0 if type(b) is int else degree[b];degree[name]=da+db if op=='*' else max(da,db)
assert degree[g['output']]==402
nodes={r[0]:r for r in g['source']};todo=[g['output']];seen=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n)
 if n in nodes:todo.extend(x for x in nodes[n][2:] if isinstance(x,str))
assert seen==set(nodes)|set(g['witnesses'])|set(g['fixed_numerals']);counts=Counter(r[1] for r in g['source']);assert counts=={'*':44,'+':17,'-':14}
for p,h in pins.items():assert sha(p)==h
result={'status':'PASS','graph_sha256':sha(G),'pdf_sha256':sha(PDF),'tex_sha256':sha(TEX),'rows':75,'pdf_pages':len(pages)-1,'selectors':len(selectors),'slots':len(slots),'raw_hashes':rawhash,'operation_counts':dict(counts),'total_degree_upper':degree[g['output']],'full_modular_ray_degree':len(z)-1,'coefficient_402':z[402],'prime':P,'scope':'independent external transcription and finite polynomial check; no Lean file binding, provider ancestry or iPRA theorem'}
print(json.dumps(result,sort_keys=True))
