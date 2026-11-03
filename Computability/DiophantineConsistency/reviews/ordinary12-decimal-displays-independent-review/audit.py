#!/usr/bin/env python3
"""Read-only, independent finite audit of both decimal display drafts."""
from pathlib import Path
from hashlib import sha256
import gzip, json, re, subprocess, sys, xml.etree.ElementTree as ET

assert sys.flags.isolated and sys.flags.no_site and __debug__
HERE=Path(__file__).resolve().parent
D=HERE.parents[1]
B=D/'research/ordinary12-ipra-bridge'
F=B/'compact44-free-j-display-draft'
lean=B/'free-j-prototype/Ordinary12FreeJ.lean'
table=B/'compact44-943-table-prototype/Compact943Data.lean'
slots=B/'compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
g95=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'
g94=D/'research/ordinary12-sum-of-squares-candidate/candidate.json'
payload=D/'candidates/free-j-polarized-positive/source/positive/coefficients/payloads'
pins={lean:'542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a',table:'10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',slots:'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',g95:'2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22',g94:'dc13e87a45a687e99e9bcb1cd3276e7c80d3e014bb7f51074084ca3214ac45ee',F/'equation94.tex':'6b46ce3af0251306aac29a5c58618e5b7dc0426b9eb7984336192566b8b4404b',F/'equation94.pdf':'8cb3727827774a3ac32f7eac87915a7c007a0d5511057aab34a4b7a1486c33d4',F/'equation.tex':'906119f203eb65d616e0845c8abfbff98f26f0d1c0a30b8f4de9100a28c10b38',F/'equation.pdf':'9cd26fe9ce325a6a92fa8f2f54ede26eb37936bc7a5217eb71d32481de3c912e'}
def digest(p): return sha256(p.read_bytes()).hexdigest()
def need(c,m):
    if not c: raise ValueError(m)
def checkpins():
    for p,v in pins.items(): need(digest(p)==v,'pin '+str(p))
checkpins()
source=lean.read_text(); chunk=source.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0]
leanrows=[]
for line in chunk.splitlines():
    if not line.strip(): continue
    m=re.fullmatch(r'\s*let (\w+) := (\w+) ([*+\-]) (\w+)\s*',line)
    need(m is not None,'unparsed Lean graph')
    name,a,op,b=m.groups(); leanrows.append([name,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
parent=json.loads(g95.read_text()); square=json.loads(g94.read_text())
need(leanrows==parent['source'] and len(leanrows)==95,'Lean/JSON parent')
need(square['source'][:89]==leanrows[:89] and square['source'][89:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Nsq','*','N','N'],['sum01','+','A0sq','A1sq'],['P12','+','sum01','Nsq']], 'square replacement')
w=['J','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']; ports=['beta','K0','MC','MF']
for i,name in enumerate(w): need(f'let {name} : Expr (Fin 12) := .var {i}' in source,'Lean witness')
for i,name in enumerate(ports): need(f'let {name} : Expr (Fin 12) := .constant (p {i})' in source,'Lean port')
rawtable=table.read_text().split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',rawtable)]
need(len(rows)==943,'row count')
select=[1+1024*(2**41-(a+256*b+2**17*c+2**25*d+127*2**34)) for a,b,c,d in rows]
slottext=slots.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0]
lambda_source=[int(x.strip()) for x in slottext.split(',')]
need(len(lambda_source)==41,'slot count')
results={}
for count,graph,stem,builds in [(94,square,'equation94',(4,5)),(95,parent,'equation',(2,3))]:
    need(graph['witnesses']==w and graph['fixed_numerals']==ports and graph['domain']=='strictly positive integers' and graph['output']=='P12','graph metadata')
    tex=(F/(stem+'.tex')).read_text(); pdf=F/(stem+'.pdf')
    for b in builds:
        need((F/f'build-attempt{b:02d}'/'equation.tex').read_bytes()==tex.encode() and (F/f'build-attempt{b:02d}'/'equation.pdf').read_bytes()==pdf.read_bytes(),'published vs build')
    need(r'a,b,c,d,e,f,g,h,i,j,k,\ell\in\mathbb Z_{>0}' in tex and (r'\boxed{\mathtt{r%02d}=0}'%count) in tex,'domain/equation')
    names=dict(zip(w,list('abcdefghijk')+['ℓ'])); names.update(dict(zip(ports,['β','κ','μ','ν'])))
    texnames=dict(zip(w,list('abcdefghijk')+[r'\ell']));texnames.update(dict(zip(ports,[r'\beta',r'\kappa',r'\mu',r'\nu'])))
    expectedpdf={}; expectedtex=[]; refs={}
    def resolve(d,a): return str(a) if isinstance(a,int) else d[a]
    for i,(name,op,a,b) in enumerate(graph['source'],1):
        label=f'r{i:02d}'; token=r'\mathtt{'+label+'}'
        expectedtex.append((token,resolve(texnames,a),{'*':r'\cdot','+':'+','-':'-'}[op],resolve(texnames,b)))
        expectedpdf[label]=(resolve(names,a),op,resolve(names,b));refs[name]=(a,b)
        names[name]=label;texnames[name]=token
    need(names['P12']==f'r{count:02d}','output')
    todo=['P12'];live=set()
    while todo:
        t=todo.pop()
        if t in refs and t not in live: live.add(t);todo.extend(refs[t])
    need(len(live)==count,'unreachable gate')
    graphtex=tex.split('% BEGIN GRAPH ROWS',1)[1].split('% END GRAPH ROWS',1)[0]
    ops=re.findall(r'\\\((\\mathtt\{r\d{2}\})\s*=\s*(\\mathtt\{r\d{2}\}|\\\w+|[a-k]|\d+)\s*(\\cdot|[+\-])\s*(\\mathtt\{r\d{2}\}|\\\w+|[a-k]|\d+)\\\)',graphtex)
    need(ops==expectedtex,'TeX graph transcription')
    extract=subprocess.run(['pdftotext','-layout',str(pdf),'-'],capture_output=True,text=True,check=True,timeout=30)
    need(not extract.stderr,'PDF text stderr'); text=extract.stdout.replace('µ','μ')
    matches=re.findall(r'\b(r\d{2})\s*=\s*(r\d{2}|[a-kℓβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-kℓβκμν]|\d+)',text.split('\f')[0])
    observed={k:(a,{'+':'+','−':'-','·':'*'}[o],b) for k,a,o,b in matches}
    need(len(matches)==count and observed==expectedpdf,'PDF graph extraction')
    need(re.search(rf'only unknowns are a, b, c, d, e, f, g, h, i, j, k, ℓ ∈ Z>0',text) and f'The equation is r{count:02d} = 0' in text,'PDF domain/equation')
    printed=[int(t) for t in re.findall(r'(?<!\d)\d{14}(?!\d)',tex.split('% BEGIN SELECTORS',1)[1].split('% END SELECTORS',1)[0])]
    pdfprinted=[int(t) for t in re.findall(r'(?<!\d)\d{14}(?!\d)',text.split('Decimal selector list.',1)[1])]
    need(printed==pdfprinted==select,'selector list order')
    slotpart=re.search(r'\\lambda=\{\}&\((.*?)\)\.',tex,re.S)
    need(slotpart is not None and [int(x) for x in re.findall(r'\d+',slotpart.group(1))]==lambda_source,'slot text')
    # Formula snippets reviewed independently and required byte-for-byte after TeX formatting is removed.
    clean=re.sub(r'\s+','',tex).replace('\\\\','').replace('&','').replace('\\quad','')
    formulas=[r'\rho=2^{67}',r'\beta=\rho^{8807}-1',r'\mathcalS={}\bigl(\{0,\ldots,942\}\cup\{983,\ldots,992\}\cup\{1003,\ldots,1011\}\cup\{1013,\ldots,1031\}\cup\{1063,1064,1095,2195,3296\}\bigr)\setminus\{1\}',r'\mu={}\beta-\sum_{u\in\mathcalS}\rho^u-2\rho^{1063}',r'\nu={}\beta+4+\sum_{u=1013}^{1022}\rho^u+\sum_{u=1065}^{1073}\rho^u+\rho^{2195}+\rho^{3296}+(2^{51}-2)(\rho^{4393}+\rho^{5495})+(2^{65}-1)\sum_{u=8792}^{8804}\rho^u+(2^{19}-1)\rho^{8805}',r'\kappa={}\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}+\sum_{u=0}^{942}\sigma_u(\rho^{4393-u}+\rho^{5495-u})+\sum_{u=0}^{40}2^{10+u}(\rho^{4393-\lambda_u}+\rho^{5495-\lambda_u})']
    need(all(f in clean for f in formulas),'formula text')
    rho=2**67;beta=rho**8807-1
    support=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296};support.remove(1)
    mu=beta-sum(rho**u for u in support)-2*rho**1063
    nu=beta+4+sum(rho**u for u in range(1013,1023))+sum(rho**u for u in range(1065,1074))+rho**2195+rho**3296+(2**51-2)*(rho**4393+rho**5495)+(2**65-1)*sum(rho**u for u in range(8792,8805))+(2**19-1)*rho**8805
    k=sum(rho**i for i in (30,62,1100,2201,8849))+sum(x*(rho**(4393-i)+rho**(5495-i)) for i,x in enumerate(printed))+sum(2**(10+i)*(rho**(4393-x)+rho**(5495-x)) for i,x in enumerate(lambda_source))
    coeff={}
    for key,v in [('beta',beta),('K',k),('MC',mu),('MF_source',nu)]:
        raw=gzip.decompress((payload/(key+'.bin.gz')).read_bytes())
        need(int.from_bytes(raw,'little')==v,'coefficient integer '+key)
        coeff[key]=sha256(raw).hexdigest()
    bbox=subprocess.run(['pdftotext','-bbox',str(pdf),'-'],capture_output=True,text=True,check=True,timeout=30)
    need(not bbox.stderr,'bbox extraction stderr')
    root=ET.fromstring(re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]', '', bbox.stdout));pages=root.findall('.//{*}page');need(len(pages)==4,'page count')
    minmargin=1000.; wordcount=0
    for p in pages:
        width=float(p.attrib['width']);height=float(p.attrib['height']);need((width,height)==(612.,792.),'page dimensions')
        for word in p.findall('.//{*}word'):
            a=word.attrib;x0=float(a['xMin']);y0=float(a['yMin']);x1=float(a['xMax']);y1=float(a['yMax'])
            need(0<=x0<=x1<=width and 0<=y0<=y1<=height,'clipped PDF word')
            minmargin=min(minmargin,x0,y0,width-x1,height-y1);wordcount+=1
    results[str(count)]={'rows':len(ops),'live':len(live),'selectors':len(printed),'slots':len(lambda_source),'raw_coefficient_hashes':coeff,'pdf_text_words':wordcount,'minimum_bbox_margin_points':round(minmargin,3),'tex_sha256':digest(F/(stem+'.tex')),'pdf_sha256':digest(pdf)}
checkpins()
print(json.dumps({'status':'PASS_INDEPENDENT_FINITE_DISPLAY_REVIEW','results':results,'scope':'Read-only external parser, arithmetic, pdftotext and sampled pins; not Lean file/PDF/iPRA proof or fresh Lean replay.'},indent=2,sort_keys=True))
