#!/usr/bin/env python3
"""Independent read-only review of the 91-row decimal TeX/PDF display."""
from hashlib import sha256
from pathlib import Path
import gzip,json,re,subprocess,sys,xml.etree.ElementTree as ET
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-xq91-decimal-display';G=D/'research/ordinary12-xq91-candidate/candidate.json'
REF=D/'research/ordinary12-qcube92-decimal-display/equation.pdf'
ROWS=D/'research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean'
SLOTS=D/'research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
C=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients';BIND=C/'BINDING.json'
O=P/'observations/checks01';PDF=P/'equation.pdf';TEX=P/'equation.tex'
PIN={G:'fde7510bbc984b7160e92ed5caff260fc90a25c9c24437efbf5c2f40c3f92513',
 PDF:'ff67d52fcc8d2809772896c21c68b5f204e1c4fe577f975650b3a3931ba90133',
 TEX:'88ccf8f71a4e9adf341912cd5e550cafca51e60245ef8fce76c3b4223607241b',
 P/'README.md':'016ad6a5356ef4aae164ae84908d1c1370ed5be966c07d9c73f7c127eae263ec',
 P/'check_display.py':'8f01b38e86b7a6948eb019352fdeb245f160cf3ab48d4bc33f1296ec81dabd78',
 P/'independent_check.py':'78d4f5d83cac5e5b13a01c807f77949d0d32b1774b10e0a2721c0a875788714f',
 O/'terminal.json':'df45e54c382226f35dde2ced20e51fa136b62efb5f6d861870690c3244906dfa',
 REF:'9b7803603e0f9237c90f30f6b14d4957ad0849b9f1765099e981403849d0dc07',
 ROWS:'10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
 SLOTS:'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',
 BIND:'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
 D/'equation.tex':'94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635',
 D/'equation.pdf':'23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6'}
def need(x,m):
 if not x:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def extract(path,mode):
 r=subprocess.run(['pdftotext',mode,str(path),'-'],capture_output=True,text=True,check=True,timeout=60);need(not r.stderr,'pdftotext stderr');return r.stdout
for p,h in PIN.items():need(sha(p)==h,'input hash mismatch '+str(p))
g=json.loads(G.read_text());tex=TEX.read_text();need(g['operations']==len(g['source'])==91 and g['output']=='P12','graph metadata')
need(g['witnesses']==['J','F','alpha','t','T','w','s','r','eta','zeta','n','gamma'] and g['fixed_numerals']==['beta','K0','MC','MF'],'graph leaf order')
for fn in ('equation.tex','equation.pdf'):
 need((P/'build01'/fn).read_bytes()==(P/'build02'/fn).read_bytes()==(P/fn).read_bytes(),'repeated build mismatch '+fn)
for build in ('build01','build02'):
 need('Overfull \\hbox' not in (P/build/'pdflatex.stdout').read_text(),'overfull box '+build)
text=extract(PDF,'-layout').replace('µ','μ');ref=extract(REF,'-layout').replace('µ','μ');pages=text.split('\f');reference=ref.split('\f')
need(len(pages)==len(reference)==5 and pages[-1]==reference[-1]=='','PDF page count')
need(pages[1:]==reference[1:],'constant/selector pages differ from separately checked 92 PDF text')
flat=' '.join(pages[0].split());need('exact degree 172; 91 evaluator operations' in flat,'degree/operation label')
need('The only unknowns are a, b, c, d, e, f, g, h, i, j, k, ℓ' in flat and 'The equation is r91 = 0' in flat,'unknowns or equation')
need('using ordinary integer arithmetic; subtraction is integer subtraction, and intermediate values may be negative.' in flat,'integer arithmetic notice')
# Reconstruct all TeX and PDF rows from the pinned graph, keeping their two
# renderings independent of either author's row parser.
pattern=r'\b(r\d{2})\s*=\s*(r\d{2}|[a-kℓβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-kℓβκμν]|\d+)'
matches=re.findall(pattern,pages[0]);pdfrows={n:(x,{'+':'+','−':'-','·':'*'}[op],y) for n,x,op,y in matches}
need(len(matches)==len(pdfrows)==91,'PDF rows missing/duplicated')
pdfnames=dict(zip(g['witnesses'],list('abcdefghijk')+['ℓ']));pdfnames.update({'beta':'β','K0':'κ','MC':'μ','MF':'ν'})
texnames=dict(zip(g['witnesses'],list('abcdefghijk')+[r'\ell']));texnames.update({'beta':r'\beta','K0':r'\kappa','MC':r'\mu','MF':r'\nu'})
expectedtex=[]
for i,(n,op,x,y) in enumerate(g['source'],1):
 def tok(mapping,x):return str(x) if type(x) is int else mapping[x]
 reg=f'r{i:02d}';need(pdfrows.get(reg)==(tok(pdfnames,x),op,tok(pdfnames,y)),'PDF row differs '+reg)
 expectedtex.append(r'\(\mathtt{'+reg+'} = '+tok(texnames,x)+' '+(r'\cdot' if op=='*' else op)+' '+tok(texnames,y)+r'\)\\')
 need(n not in pdfnames and n not in texnames,'duplicate graph node');pdfnames[n]=reg;texnames[n]=r'\mathtt{'+reg+'}'
block=tex.split('% BEGIN GRAPH ROWS',1)[1].split('% END GRAPH ROWS',1)[0]
actualtex=[line for line in block.splitlines() if line.startswith(r'\(\mathtt{')]
need(actualtex==expectedtex and pdfnames[g['output']]=='r91','TeX row/output mismatch')
# Reconstruct ordered slots and decimal selectors from the PDF, preserving
# each leading zero. The four integers are recomputed with bit shifts.
slots_pdf=[int(x) for x in re.findall(r'\d+',pages[1].split('λ = (',1)[1].split(').',1)[0])]
slots=[int(x.strip()) for x in SLOTS.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0].split(',')]
need(len(slots)==41 and slots_pdf==slots,'PDF slot list mismatch')
rawrows=ROWS.read_text().split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',rawrows)]
selectors=[1+1024*((1<<41)-(w+(n<<8)+(p<<17)+(s<<25)+(127<<34))) for w,n,p,s in rows]
blocks=re.findall(r'(?<!\d)\d{14}(?!\d)',text.split('Decimal selector list.',1)[1]);need(len(rows)==len(blocks)==943 and blocks==[f'{x:014d}' for x in selectors],'PDF selector blocks')
def power(k):return 1<<(67*k)
beta=power(8807)-1;support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
mc=beta-sum(map(power,support))-2*power(1063)
mf=(beta+4+sum(map(power,range(1013,1023)))+sum(map(power,range(1065,1074)))+power(2195)+power(3296)+((1<<51)-2)*(power(4393)+power(5495))+((1<<65)-1)*sum(map(power,range(8792,8805)))+((1<<19)-1)*power(8805))
kappa=(sum(map(power,(30,62,1100,2201,8849)))+sum(z*(power(4393-i)+power(5495-i)) for i,z in enumerate(selectors))+sum((1<<(10+i))*(power(4393-u)+power(5495-u)) for i,u in enumerate(slots)))
meta=json.loads(BIND.read_text());payloads={};coeffhash={}
for name,val in [('beta',beta),('K0',kappa),('MC',mc),('MF',mf)]:
 entry=meta['ports'][name];path=C/entry['file'];z=path.read_bytes();raw=gzip.decompress(z)
 need(sha256(z).hexdigest()==entry['sha256_gzip'] and sha256(raw).hexdigest()==entry['sha256_raw'] and len(raw)==entry['raw_bytes'],'payload hash '+name)
 need(val.to_bytes(len(raw),'little')==raw,'coefficient value '+name);payloads[path]=entry['sha256_gzip'];coeffhash[name]=entry['sha256_raw']
bbox=extract(PDF,'-bbox');xml=ET.fromstring(re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]','',bbox));bp=xml.findall('.//{*}page');need(len(bp)==4,'bounding-box pages');margin=1000.;count=0
for page in bp:
 w=float(page.attrib['width']);h=float(page.attrib['height'])
 for word in page.findall('.//{*}word'):
  a,b,c,d=map(float,(word.attrib['xMin'],word.attrib['xMax'],word.attrib['yMin'],word.attrib['yMax']));need(0<=a<=b<=w and 0<=c<=d<=h,'clipped PDF word');margin=min(margin,a,c,w-b,h-d);count+=1
need(count>0,'empty bounding boxes')
# Re-run the retained separate checks and compare their captured output.
receipt=json.loads((O/'terminal.json').read_text());need(receipt['input_sha256_before']==receipt['input_sha256_after'],'author input drift')
for item in receipt['checks']:
 name=item['name'];r=subprocess.run([sys.executable,'-I','-S','-B',str(P/(name+'.py'))],capture_output=True,check=True)
 need(not r.stderr and r.stdout==(O/(name+'.stdout')).read_bytes() and sha(O/(name+'.stdout'))==item['stdout_sha256'],'author check mismatch '+name)
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-xq91-independent/check.py')],capture_output=True,check=True)
proof=json.loads(prior.stdout);need(not prior.stderr and proof['new_live_operations']==91 and proof['upper_bounds']['P12']==proof['degree_lower_witness']['degree']==172,'independent degree/graph review failed')
for path,h in {**PIN,**payloads}.items():need(sha(path)==h,'input changed during check '+str(path))
print(json.dumps({'status':'PASS','graph_rows':len(pdfrows),'pdf_pages':len(bp),'decimal_selectors':len(blocks),'slots':len(slots),
 'coefficient_sha256':coeffhash,'pdf_constant_pages_equal_92_text':True,'degree_external':172,
 'bbox_words':count,'minimum_bbox_margin_points':round(margin,3),'separate_author_checks':'PASS',
 'scope':'external TeX/PDF text and coefficient comparison, not Lean file/PDF or iPRA proof'},indent=2,sort_keys=True))
