#!/usr/bin/env python3
"""Independently check extracted PDF graph, fixed constants and layout."""
from hashlib import sha256
from pathlib import Path
import gzip, json, re, subprocess, xml.etree.ElementTree as ET
H=Path(__file__).resolve().parent;D=H.parents[1]
G=D/'research/ordinary12-qcube92-candidate/candidate.json';PDF=H/'equation.pdf';TEX=H/'equation.tex'
REF=D/'research/ordinary12-ipra-bridge/compact44-free-j-display-v2/equation94.pdf'
DATA=D/'research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean'
SLOTS=D/'research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
C=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients';BIND=C/'BINDING.json'
PINS={G:'3a21d323adb96788a4b46c0b33800e07f2d1cb708b5c3c53ab709f6e186acee3',
 PDF:'9b7803603e0f9237c90f30f6b14d4957ad0849b9f1765099e981403849d0dc07',
 TEX:'eacbe2fd9a52fe599fae4a51afb58ae588d21e3bec7eefc48c86bae33d3c8bfd',
 REF:'249db24776757d26a7ea9e5b90f90e8deb0e0ef09cd493b6c6841c2e7d8ed7c7',
 DATA:'10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
 SLOTS:'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',
 BIND:'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'}
def need(x,m):
 if not x:raise SystemExit(m)
def sha(p):return sha256(p.read_bytes()).hexdigest()
def extract(p,flag):
 r=subprocess.run(['pdftotext',flag,str(p),'-'],capture_output=True,text=True,check=True,timeout=60);need(not r.stderr,'pdftotext stderr');return r.stdout
for p,h in PINS.items():need(sha(p)==h,'pinned input mismatch: '+str(p))
g=json.loads(G.read_text());need(len(g['source'])==g['operations']==92,'graph count')
need(g['witnesses']==['J','F','alpha','t','T','X','s','r','eta','zeta','n','gamma'],'witness order')
need(g['fixed_numerals']==['beta','K0','MC','MF'] and g['domain']=='strictly positive integers','port/domain')
t=extract(PDF,'-layout').replace('µ','μ');ref=extract(REF,'-layout').replace('µ','μ');pages=t.split('\f');rp=ref.split('\f')
need(len(pages)==len(rp)==5 and pages[-1]==rp[-1]=='','page count');need(pages[1:]==rp[1:],'fixed-coefficient PDF text differs from independently reviewed reference')
flat=' '.join(pages[0].split())
need('using ordinary integer arithmetic; subtraction is integer subtraction, and intermediate values may be negative.' in flat,'integer arithmetic notice')
need('The only unknowns are a, b, c, d, e, f, g, h, i, j, k, ℓ' in flat and 'The equation is r92 = 0' in flat,'unknowns/equation')
pat=r'\b(r\d{2})\s*=\s*(r\d{2}|[a-kℓβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-kℓβκμν]|\d+)'
found=re.findall(pat,pages[0]);seen={n:(x,{'+':'+','−':'-','·':'*'}[op],y) for n,x,op,y in found};need(len(found)==len(seen)==92,'PDF row count')
refs=dict(zip(g['witnesses'],list('abcdefghijk')+['ℓ']));refs.update({'beta':'β','K0':'κ','MC':'μ','MF':'ν'})
for i,(name,op,x,y) in enumerate(g['source'],1):
 def tok(t):return str(t) if type(t) is int else refs[t]
 key=f'r{i:02d}';need(key in seen and seen[key]==(tok(x),op,tok(y)),'PDF operation mismatch '+key);need(name not in refs,'duplicate node');refs[name]=key
need(refs[g['output']]=='r92','output')
part=pages[1].split('λ = (',1)[1].split(').',1)[0];printed_slots=[int(x) for x in re.findall(r'\d+',part)]
slottext=SLOTS.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0];slots=[int(x.strip()) for x in slottext.split(',')]
need(len(slots)==41 and printed_slots==slots,'PDF slots')
rtext=DATA.read_text().split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',rtext)]
sel=[1+1024*(2**41-(w+256*n+2**17*p+2**25*s+127*2**34)) for w,n,p,s in rows]
printed=re.findall(r'(?<!\d)\d{14}(?!\d)',t.split('Decimal selector list.',1)[1]);need(len(rows)==len(sel)==len(printed)==943 and printed==[f'{n:014d}' for n in sel],'PDF selector blocks')
rho=2**67;beta=rho**8807-1
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
mc=beta-sum(rho**u for u in support)-2*rho**1063
mf=(beta+4+sum(rho**u for u in range(1013,1023))+sum(rho**u for u in range(1065,1074))+rho**2195+rho**3296+(2**51-2)*(rho**4393+rho**5495)+(2**65-1)*sum(rho**u for u in range(8792,8805))+(2**19-1)*rho**8805)
kappa=(rho**30+rho**62+rho**1100+rho**2201+rho**8849+sum(z*(rho**(4393-i)+rho**(5495-i)) for i,z in enumerate(sel))+sum(2**(10+i)*(rho**(4393-u)+rho**(5495-u)) for i,u in enumerate(slots)))
binding=json.loads(BIND.read_text());payloads={};raw_hashes={}
for name,value in [('beta',beta),('K0',kappa),('MC',mc),('MF',mf)]:
 meta=binding['ports'][name];p=C/meta['file'];data=p.read_bytes();raw=gzip.decompress(data)
 need(sha256(data).hexdigest()==meta['sha256_gzip'] and sha256(raw).hexdigest()==meta['sha256_raw'] and len(raw)==meta['raw_bytes'],'payload hash '+name)
 need(value.to_bytes(len(raw),'little')==raw,'whole coefficient mismatch '+name);payloads[p]=meta['sha256_gzip'];raw_hashes[name]=meta['sha256_raw']
bbox=extract(PDF,'-bbox');root=ET.fromstring(re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]','',bbox));bp=root.findall('.//{*}page');need(len(bp)==4,'bbox page count');margin=1000.;words=0
for page in bp:
 width=float(page.attrib['width']);height=float(page.attrib['height'])
 for word in page.findall('.//{*}word'):
  x0=float(word.attrib['xMin']);x1=float(word.attrib['xMax']);y0=float(word.attrib['yMin']);y1=float(word.attrib['yMax']);need(0<=x0<=x1<=width and 0<=y0<=y1<=height,'PDF word outside page');margin=min(margin,x0,y0,width-x1,height-y1);words+=1
need(words>0,'empty PDF')
for p,h in {**PINS,**payloads}.items():need(sha(p)==h,'input changed: '+str(p))
print(json.dumps({'status':'PASS_INDEPENDENT_92_PDF_CHECK','graph_rows':len(seen),'pdf_pages':len(bp),
 'pdf_constant_pages_match_independently_reviewed_v2_94':True,'decimal_selectors':len(printed),'slot_count':len(slots),
 'coefficient_raw_sha256':raw_hashes,'bbox_words':words,'minimum_bbox_margin_points':round(margin,3),
 'pdf_sha256':sha(PDF),'tex_sha256':sha(TEX),'scope':'external graph/PDF text, coefficient payload and bounding-box checks; no Lean file/PDF theorem or internal iPRA proof'},indent=2,sort_keys=True))
