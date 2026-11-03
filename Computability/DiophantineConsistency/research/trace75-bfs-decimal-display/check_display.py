#!/usr/bin/env python3
"""Independently check extracted PDF graph, fixed constants and layout."""
from hashlib import sha256
from pathlib import Path
import gzip, json, re, subprocess, sys, xml.etree.ElementTree as ET
if sys.flags.optimize: raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1]
G=D/'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json';PDF=H/'equation.pdf';TEX=H/'equation.tex'
REF=D/'research/ten-positive-80-bfs-decimal-display/equation.tex';REFPDF=REF.with_suffix('.pdf')
DATA=D/'research/indexed-tile-enumeration/TILES.json'
SLOTS=D/'research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
C=D/'research/ten-positive-unshift-t-finite/coefficients'
PINS={G:'8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
 PDF:'86ad6a7ca7e7125818ff08014cb03c04540bb531b072a75cfa02ae29b0e8edd6',
 TEX:'98994625e4b56ce927b3c8792ce2411e83cc4df254a8ec8ee9652ddaf710d388',
 REF:'be7181e835a2b530da007b7b856ea9a799db2f2ad05aef8036a3a95ed21cd849',
 REFPDF:'412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7',
 DATA:'f06d1b9858281f1adcbc431d3c0df9b07df1a231793629650b2d3c09eac56549',
 SLOTS:'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae'}
def need(x,m):
 if not x:raise SystemExit(m)
def sha(p):return sha256(p.read_bytes()).hexdigest()
def extract(p,flag):
 r=subprocess.run(['pdftotext',flag,str(p),'-'],capture_output=True,text=True,check=True,timeout=60);need(not r.stderr,'pdftotext stderr');return r.stdout
for p,h in PINS.items():need(sha(p)==h,'pinned input mismatch: '+str(p))
g=json.loads(G.read_text());need(len(g['source'])==g['operations']==75,'graph count')
need(g['witnesses']==['J','F','alpha','i','T','w','s','n','eta','zeta'],'witness order')
need(g['fixed_numerals']==['beta','K0','MC','MF'] and g['domain']=='strictly positive integers','port/domain')
t=extract(PDF,'-layout').replace('µ','μ');pages=t.split('\f')
need(len(pages)==5 and pages[-1]=='','page count')
refpages=extract(REFPDF,'-layout').replace('µ','μ').split('\f')
need(len(refpages)==5 and pages[1].split('Decimal selector list.',1)[0]==refpages[1].split('Decimal selector list.',1)[0],'PDF coefficient formulas differ')
start=r'\textbf{The four fixed integers.}';end=r'\textbf{Decimal selector list.}'
need(TEX.read_text().split(start,1)[1].split(end,1)[0]==REF.read_text().split(start,1)[1].split(end,1)[0],'fixed coefficient formulas differ')
flat=' '.join(pages[0].split())
need('using ordinary integer arithmetic; subtraction is integer subtraction, and intermediate values may be negative.' in flat,'integer arithmetic notice')
need('The only unknowns are a, b, c, d, e, f, g, h, i, j' in flat and 'The equation is r75 = 0' in flat,'unknowns/equation')
pat=r'\b(r\d{2})\s*=\s*(r\d{2}|[a-jβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-jβκμν]|\d+)'
found=re.findall(pat,pages[0]);seen={n:(x,{'+':'+','−':'-','·':'*'}[op],y) for n,x,op,y in found};need(len(found)==len(seen)==75,'PDF row count')
refs=dict(zip(g['witnesses'],list('abcdefghij')));refs.update({'beta':'β','K0':'κ','MC':'μ','MF':'ν'})
for i,(name,op,x,y) in enumerate(g['source'],1):
 def tok(t):return str(t) if type(t) is int else refs[t]
 key=f'r{i:02d}';need(key in seen and seen[key]==(tok(x),op,tok(y)),'PDF operation mismatch '+key);need(name not in refs,'duplicate node');refs[name]=key
need(refs[g['output']]=='r75','output')
part=pages[1].split('λ = (',1)[1].split(').',1)[0];printed_slots=[int(x) for x in re.findall(r'\d+',part)]
slottext=SLOTS.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0];slots=[int(x.strip()) for x in slottext.split(',')]
need(len(slots)==41 and printed_slots==slots,'PDF slots')
rows=json.loads(DATA.read_text())
sel=[1+1024*(2**41-(w+256*n+2**17*p+2**25*s+127*2**34)) for w,n,p,s in rows]
printed=re.findall(r'(?<!\d)\d{14}(?!\d)',t.split('Decimal selector list.',1)[1]);need(len(rows)==len(sel)==len(printed)==943 and printed==[f'{n:014d}' for n in sel],'PDF selector blocks')
rho=2**67;beta=rho**8807-1
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
mc=beta-sum(rho**u for u in support)-2*rho**1063
mf=(beta+4+sum(rho**u for u in range(1013,1023))+sum(rho**u for u in range(1065,1074))+rho**2195+rho**3296+(2**51-2)*(rho**4393+rho**5495)+(2**65-1)*sum(rho**u for u in range(8792,8805))+(2**19-1)*rho**8805)
kappa=(rho**30+rho**62+rho**1100+rho**2201+rho**8849+sum(z*(rho**(4393-i)+rho**(5495-i)) for i,z in enumerate(sel))+sum(2**(10+i)*(rho**(4393-u)+rho**(5495-u)) for i,u in enumerate(slots)))
binding=g['coefficient_binding'];payloads={};raw_hashes={}
for name,value in [('beta',beta),('K0',kappa),('MC',mc),('MF',mf)]:
 meta=binding['ports'][name];p=C/meta['file'];data=p.read_bytes();raw=gzip.decompress(data)
 need(sha256(data).hexdigest()==meta['parent_gzip_sha256'] and sha256(raw).hexdigest()==meta['raw_sha256'],'payload hash '+name)
 need(value.to_bytes(len(raw),'little')==raw,'whole coefficient mismatch '+name);payloads[p]=meta['parent_gzip_sha256'];raw_hashes[name]=meta['raw_sha256']
bbox=extract(PDF,'-bbox');root=ET.fromstring(re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]','',bbox));bp=root.findall('.//{*}page');need(len(bp)==4,'bbox page count');margin=1000.;words=0
for page in bp:
 width=float(page.attrib['width']);height=float(page.attrib['height'])
 for word in page.findall('.//{*}word'):
  x0=float(word.attrib['xMin']);x1=float(word.attrib['xMax']);y0=float(word.attrib['yMin']);y1=float(word.attrib['yMax']);need(0<=x0<=x1<=width and 0<=y0<=y1<=height,'PDF word outside page');margin=min(margin,x0,y0,width-x1,height-y1);words+=1
need(words>0,'empty PDF')
for p,h in {**PINS,**payloads}.items():need(sha(p)==h,'input changed: '+str(p))
print(json.dumps({'status':'PASS_75_PDF_CHECK','graph_rows':len(seen),'pdf_pages':len(bp),
 'tex_and_pdf_fixed_formulas_match_reviewed_original':True,'decimal_selectors':len(printed),'slot_count':len(slots),
 'coefficient_raw_sha256':raw_hashes,'bbox_words':words,'minimum_bbox_margin_points':round(margin,3),
 'pdf_sha256':sha(PDF),'tex_sha256':sha(TEX),'scope':'external graph/PDF text, coefficient payload and bounding-box checks; no Lean file/PDF theorem or internal iPRA proof'},indent=2,sort_keys=True))
