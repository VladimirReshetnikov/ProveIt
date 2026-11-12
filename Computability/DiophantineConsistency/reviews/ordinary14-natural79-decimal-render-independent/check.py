#!/usr/bin/env python3
"""Independent PDF/TeX, graph and coefficient comparison, no Lean or writes."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural79-decimal-render-candidate'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
tex=pin(P/'equation.tex','a9a6ae35d88e3f842d5493fbe6c7f6460285a3d3ae211a40c6b0375ae350ec20').decode()
pdf=pin(P/'equation.pdf','096455e415508167ea768f037aa18cd8fde619efd0e0886d800a94d830fa21e8')
seed=pin(P/'DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297').decode().strip()
graph=json.loads(pin(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
lean=pin(D/'research/ordinary14-natural79-corrected-reflection-overlay/source/P79NaturalForcedW.lean.src','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36').decode()
table=pin(D/'Lean/DiophantineConsistency/Compact44/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8').decode()
kern=pin(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean','9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55').decode()
binding=json.loads(pin(D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
result=json.loads(pin(P/'result.json','38220702aeef03b916e7188a9bb76a213d3b9606d386dd15c7072aeb9e2711f8'))
render=json.loads(pin(P/'render-result.json','2d5ce9cf5a93ed42886d9c683eddfa063570f2ed466e269c20400b594c4e2392'))
# Independently parse every literal source row and compare graph JSON exactly.
block=lean.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('-- END LITERAL GRAPH',1)[0]
rows=[]
for line in block.splitlines():
 if not line.strip():continue
 m=re.fullmatch(r'\s*let\s+(\w+)\s*:=\s*(\w+)\s*([+*\-])\s*(\w+)\s*',line);assert m,line
 def atom(x):return int(x) if x.isdigit() else x
 rows.append([m[1],m[3],atom(m[2]),atom(m[4])])
assert rows==graph['source'] and len(rows)==graph['operations']==79 and graph['output']=='out'
inputs=['J','F','A','f','i','T','w','s','r','e','z','y','g','h']
assert len(inputs)==len(set(inputs))==14
assert 'The unknowns, all distinct, are $'+','.join(inputs)+r'\in\mathbb N$' in tex
assert all(x not in inputs for x in ['j','k'])
assert r'(\lambda_0,\ldots,\lambda_{40})' in tex and r'(s_0,\ldots,s_{40})' not in tex
witness=dict(zip(graph['witnesses'],inputs));ports={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'}
for i,n in enumerate(graph['witnesses']):assert f'let {n} : Expr (Fin 14) := .var {i}' in lean
for i,n in enumerate(graph['fixed_numerals']):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in lean
def nm(n):
 if isinstance(n,int):return str(n)
 if n in witness:return witness[n]
 if n in ports:return ports[n]
 return r'\mathtt{v'+n.replace('_',r'\_')+'}'
def expression_row(row):
 n,op,a,b=row;return r'\noindent $'+nm(n)+' = '+nm(a)+{'*':r'\cdot ', '+':'+', '-':'-'}[op]+nm(b)+r'$\par'
actual=[x for x in tex.splitlines() if x.startswith(r'\noindent $')]
assert actual==[expression_row(r) for r in rows]
assert r'The single equation is $\boxed{\mathtt{vout}=0}$.' in tex
assert 'base-10 notation' in tex and 'base 61' not in tex.lower()
# Fixed formulas are checked literally against a separate transcription below.
for expected in [
 r'\rho=2^{67}$, $\beta=\rho^{8807}-1$',
 r'd_j=\lfloor P/10^{16j}\rfloor\bmod 10^{16}$ for $0\le j<943$',
 r'K={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}\\'+'\n'+r'&+\sum_{j=0}^{942}d_j(\rho^{4393-j}+\rho^{5495-j})\\'+'\n'+r'&+\sum_{j=0}^{40}2^{10+j}(\rho^{4393-\lambda_j}+\rho^{5495-\lambda_j}).',
 r'S={}&([0,942]\cup[983,992]\cup[1003,1011]\cup[1013,1031]\\&{}\cup\{1063,1064,1095,2195,3296\})\setminus\{1\}',
 r'\mu=\beta-\sum_{k\in S}\rho^k-2\rho^{1063}$ and $\omega=\beta+H$',
 r'H={}&4+\sum_{k=1013}^{1022}\rho^k+\sum_{k=1065}^{1073}\rho^k+\rho^{2195}+\rho^{3296}\\'+'\n'+r'&+(2^{51}-2)(\rho^{4393}+\rho^{5495})+(2^{65}-1)\sum_{k=8792}^{8804}\rho^k+(2^{19}-1)\rho^{8805}.']:
 assert expected in tex,expected
section=tex.split(r'\par\begingroup\fontsize{6}{7}\selectfont\ttfamily',1)[1].split(r'\endgroup',1)[0]
assert all(re.fullmatch(r'\d{1,75}\\par',line) for line in section.splitlines() if line.strip())
assert ''.join(line[:-4] for line in section.splitlines() if line.strip())==seed
assert len(seed)==15086 and seed.isdecimal() and seed[0]!='0'
slotsblock=tex.split(r'\begin{gathered}',1)[1].split(r'\end{gathered}',1)[0]
slots=[int(x) for x in re.findall(r'\d+',slotsblock)]
km=re.search(r'^def slots : List ℕ := \[([0-9,]+)\]$',kern,re.M);assert km
assert slots==[int(x) for x in km[1].split(',')] and len(slots)==41
# d_j are decimal blocks recovered from P from right to left, including padding.
padded=seed.zfill(16*943);assert len(padded)==16*943
ds=[int(padded[len(padded)-16*(j+1):len(padded)-16*j]) for j in range(943)]
ordered=table.split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0]
records=[]
for line in ordered.splitlines():
 m=re.fullmatch(r'\s*\((\d+), (\d+), (\d+), (\d+)\),?',line);assert m,line
 records.append(tuple(map(int,m.groups())))
assert len(records)==943
assert ds==[1+1024*((1<<41)-(a+(1<<8)*b+(1<<17)*c+(1<<25)*d+127*(1<<34))) for a,b,c,d in records]
rho=1<<67;beta=rho**8807-1
K=sum(rho**j for j in [30,62,1100,2201,8849])
K+=sum(d*(rho**(4393-j)+rho**(5495-j)) for j,d in enumerate(ds))
K+=sum(2**(10+j)*(rho**(4393-v)+rho**(5495-v)) for j,v in enumerate(slots))
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
low=beta-sum(rho**k for k in support)-2*rho**1063
high=4+sum(rho**k for k in range(1013,1023))+sum(rho**k for k in range(1065,1074))+rho**2195+rho**3296
high+=(2**51-2)*(rho**4393+rho**5495)+(2**65-1)*sum(rho**k for k in range(8792,8805))+(2**19-1)*rho**8805
computed={'beta':beta,'K0':K,'MC':low,'MF':beta+high};hashes={}
for name,value in computed.items():
 meta=binding['ports'][name];gz=(D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'/meta['path']).read_bytes()
 assert sha(gz)==meta['sha256_gzip'];raw=gzip.decompress(gz)
 assert len(raw)==meta['raw_bytes'] and sha(raw)==meta['sha256_raw'] and int.from_bytes(raw,'little')==value
 hashes[name]=sha(raw)
assert hashes==result['port_values_match_retained_gzip_bytes']
# PDF text is compared independently to every row and every decimal seed digit.
info=subprocess.run(['pdfinfo',str(P/'equation.pdf')],capture_output=True,text=True,check=True).stdout
assert re.search(r'^Pages:\s+4\s*$',info,re.M)
text=subprocess.run(['pdftotext','-raw',str(P/'equation.pdf'),'-'],capture_output=True,text=True,check=True).stdout
pdflines=text.splitlines();start=next(i for i,x in enumerate(pdflines) if x.strip().startswith('valpha ='))
end=next(i for i,x in enumerate(pdflines[start:],start) if x.strip().startswith('vout ='))
pdfrows=[' '.join(x.split()) for x in pdflines[start:end+1]]
def glyph(n):
 if isinstance(n,int):return str(n)
 if n in witness:return witness[n]
 if n in ports:return {'beta':'β','K0':'K','MC':'µ','MF':'ω'}[n]
 return 'v'+n.replace('_',' ')
expectedpdf=[' '.join((glyph(n)+' = '+glyph(a)+' '+{'*':'·','+':'+','-':'−'}[op]+' '+glyph(b)).split()) for n,op,a,b in rows]
assert pdfrows==expectedpdf,(len(pdfrows),next(((x,y) for x,y in zip(pdfrows,expectedpdf) if x!=y),None))
part=text.split('Complete decimal integer P.',1)[1].split('This is an unelaborated',1)[0]
pdfseed=''.join(line.strip() for line in part.splitlines() if re.fullmatch(r'[0-9]{1,75}',line.strip()))
assert pdfseed==seed
assert render['pdf_sha256']==sha(pdf) and render['tex_sha256']==sha(tex.encode()) and result['tex_sha256']==sha(tex.encode())
print(json.dumps({'scope':'external exact graph/decimal/byte and PDF text comparison; not Lean or document semantics',
 'tex_sha256':sha(tex.encode()),'pdf_sha256':sha(pdf),'decimal_seed_sha256':sha(seed.encode()),
 'graph_rows_source_tex_pdf':len(rows),'distinct_nonnegative_inputs':inputs,'decimal_digits':len(seed),
 'decimal_block_count':len(ds),'selector_positions':len(slots),'computed_port_raw_sha256':hashes,
 'pdf_pages':4,'pdf_seed_and_graph_rows_match':True,'beta_added_to_MF_exactly_once':True},sort_keys=True,indent=2,ensure_ascii=False))
