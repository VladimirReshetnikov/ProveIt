#!/usr/bin/env python3
"""Independent, finite display and receipt audit; no Lean theorem about files."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import gzip
import json
import re
import subprocess
import sys
import xml.etree.ElementTree as ET

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
A = D / 'research/ordinary12-direct90-decimal-display'
G = D / 'research/ordinary12-direct-main-probe/graph-dag.json'
L = G.parent / 'DirectMainGraph.lean'
DATA = D / 'research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean'
SLOTS = D / 'research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
PAY = D / 'candidates/free-j-polarized-positive/source/positive/coefficients/payloads'
REF = D / 'research/ordinary12-ipra-bridge/compact44-free-j-display-v2/equation94.pdf'
RECEIPT = A / 'observations/checks01/terminal.json'
PINS = {G:'82dd1f55f67ef3487509a6d4d31ef085d5d4813c11df43be40570a3293a8b430',
 L:'6e465bd6329d4932b3c75e2984f9b771b5ae99d329f946aebba88abaa283c216',
 DATA:'10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
 SLOTS:'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',
 RECEIPT:'099eb1c6a83144c7a30177141f6968e75f54fc0d2b54a61d8daa59103d1c2f33',
 REF:'249db24776757d26a7ea9e5b90f90e8deb0e0ef09cd493b6c6841c2e7d8ed7c7'}
def need(x, why):
    if not x: raise RuntimeError(why)
def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def pdf_text(p, option):
    run = subprocess.run(['pdftotext',option,str(p),'-'], capture_output=True, timeout=60)
    need(run.returncode == 0 and not run.stderr, 'pdftotext failure')
    return run.stdout.decode()
for p,h in PINS.items(): need(digest(p)==h, 'input pin drift: '+str(p))
receipt=json.loads(RECEIPT.read_text())
need(receipt['input_sha256_before']==receipt['input_sha256_after'], 'capture had changing inputs')
for p,h in receipt['input_sha256_before'].items(): need(digest(p)==h, 'captured input changed: '+p)
for row in receipt['checks']:
    need(row['exit']==0 and row['name'] in ('check_display','independent_check'), 'captured check failed')
    for typ in ('stdout','stderr'):
        p=RECEIPT.parent/(row['name']+'.'+typ)
        need(digest(p)==row[typ+'_sha256'], 'captured log mismatch: '+str(p))
        if typ=='stderr': need(not p.read_bytes(), 'captured stderr nonempty')
    p=RECEIPT.parent/(row['name']+'.stdout')
    need('PASS' in json.loads(p.read_text())['status'], 'captured status')
need(len(receipt['checks'])==2 and len({x['name'] for x in receipt['checks']})==2, 'missing check')
for n in (1,2):
    b=A/f'build0{n}';result=json.loads((b/'RESULT.json').read_text())
    need(result['pdflatex_exit_code']==0 and result['status']=='EXTERNAL_DISPLAY_DRAFT_ONLY', 'build receipt')
    for kind in ('tex','pdf'):
        need(digest(b/f'equation.{kind}')==result[f'{kind}_sha256']==digest(A/f'equation.{kind}'), 'build file mismatch')
    need('Overfull \\hbox' not in (b/'pdflatex.stdout').read_text() and not (b/'pdflatex.stderr').read_bytes(), 'build log')
    for name,h in result['input_sha256'].items(): need(digest(D.parents[1]/name)==h, 'build input drift: '+name)

graph=json.loads(G.read_text()); rows=graph['source']
need(graph['domain']=='strictly positive integers' and len(rows)==graph['operations']==90, 'graph metadata')
need(len(graph['witnesses'])==len(set(graph['witnesses']))==12, 'witness count')
need(graph['fixed_numerals']==['beta','K0','MC','MF'], 'ports')
source=L.read_text().split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\nvariable {R : Type*}',1)[0]
def val(s): return int(s) if s.isdigit() else s
lean=[[n,op,val(x),val(y)] for n,x,op,y in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',source,re.M)]
need(lean==rows, 'Lean expression/source graph mismatch')
for i,n in enumerate(graph['witnesses']): need(f'  let {n} : Expr (Fin 12) := .var {i}\n' in source,'Lean witness')
for i,n in enumerate(graph['fixed_numerals']): need(f'  let {n} : Expr (Fin 12) := .constant (p {i})\n' in source,'Lean port')
need('  ⟨A0, A1, N, P12⟩' in source and graph['output']=='P12', 'Lean output')
known=set(graph['witnesses']+graph['fixed_numerals']); parents={}; mapping=dict(zip(graph['witnesses'],list('abcdefghijk')+['ℓ']));mapping.update({'beta':'β','K0':'κ','MC':'μ','MF':'ν'})
expected={}
for i,(name,op,x,y) in enumerate(rows,1):
    need(name not in known and op in ('+','-','*'), 'invalid graph node')
    def operand(z):
        need(type(z)==int and z>=0 or z in known, 'bad graph operand')
        return str(z) if type(z)==int else mapping[z]
    expected[f'r{i:02d}']=(operand(x),op,operand(y))
    parents[name]=(x,y);mapping[name]=f'r{i:02d}';known.add(name)
live=set(); stack=[graph['output']]
while stack:
    n=stack.pop()
    if n in parents and n not in live:
        live.add(n);stack.extend(parents[n])
need(len(live)==90 and Counter(r[1] for r in rows)=={'*':50,'+':23,'-':17},'graph liveness/count')
text=pdf_text(A/'equation.pdf','-layout').replace('µ','μ'); pages=text.split('\f')
need(len(pages)==5 and pages[-1]=='','PDF pages')
old=pdf_text(REF,'-layout').replace('µ','μ').split('\f')
need(pages[1:]==old[1:],'fixed-coefficient PDF pages differ from checked reference')
first=' '.join(pages[0].split())
need('The only unknowns are a, b, c, d, e, f, g, h, i, j, k, ℓ' in first and 'The equation is r90 = 0' in first and 'subtraction is integer subtraction' in first,'PDF statement')
pat=r'\b(r\d{2})\s*=\s*(r\d{2}|[a-kℓβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-kℓβκμν]|\d+)'
found=re.findall(pat,pages[0]); displayed={n:(x,{'+':'+','−':'-','·':'*'}[op],y) for n,x,op,y in found}
need(len(found)==len(displayed)==90 and displayed==expected,'PDF graph mismatch')
tex=(A/'equation.tex').read_text(); texgraph=tex.split('% BEGIN GRAPH ROWS',1)[1].split('% END GRAPH ROWS',1)[0]
tr=re.findall(r'\\mathtt\{(r\d{2})\} = (.*?) ([+\-]|\\cdot) (.*?)\\\)',texgraph)
def clean(x):
    if x.startswith('\\mathtt{'): return x[8:-1]
    return {'\\ell':'ℓ','\\beta':'β','\\kappa':'κ','\\mu':'μ','\\nu':'ν'}.get(x,x)
actual={n:(clean(x),'*' if op=='\\cdot' else op,clean(y)) for n,x,op,y in tr}
need(len(tr)==len(actual)==90 and actual==expected,'TeX graph mismatch')
rowtext=DATA.read_text().split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
table=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',rowtext)]
selectors=[1+1024*((1<<41)-(w+256*n+(1<<17)*p+(1<<25)*s+127*(1<<34))) for w,n,p,s in table]
printed=[int(x) for x in re.findall(r'(?<!\d)\d{14}(?!\d)',text.split('Decimal selector list.',1)[1])]
need(len(table)==len(selectors)==len(printed)==943 and printed==selectors, 'PDF selectors')
slots=[int(x) for x in SLOTS.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0].split(',')]
pslots=[int(x) for x in re.findall(r'\d+',pages[1].split('λ = (',1)[1].split(').',1)[0])]
need(len(slots)==41 and pslots==slots,'PDF slots')
# Independently reconstruct the fixed integers using bit positions 67*u.
bit=lambda u: 1<<(67*u)
beta=bit(8807)-1
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
mu=beta-sum(map(bit,support))-2*bit(1063)
nu=beta+4+sum(map(bit,range(1013,1023)))+sum(map(bit,range(1065,1074)))+bit(2195)+bit(3296)+((1<<51)-2)*(bit(4393)+bit(5495))+((1<<65)-1)*sum(map(bit,range(8792,8805)))+((1<<19)-1)*bit(8805)
kappa=sum(map(bit,(30,62,1100,2201,8849)))+sum(v*(bit(4393-i)+bit(5495-i)) for i,v in enumerate(printed))+sum((1<<(10+i))*(bit(4393-v)+bit(5495-v)) for i,v in enumerate(pslots))
payload_hashes={}
for name,value in (('beta',beta),('K',kappa),('MC',mu),('MF_source',nu)):
    raw=gzip.decompress((PAY/f'{name}.bin.gz').read_bytes());need(int.from_bytes(raw,'little')==value,'coefficient '+name)
    payload_hashes[name]=sha256(raw).hexdigest()
bbox=pdf_text(A/'equation.pdf','-bbox'); xml=ET.fromstring(re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]','',bbox)); margin=1000.;count=0
for page in xml.findall('.//{*}page'):
    width=float(page.attrib['width']); height=float(page.attrib['height'])
    for word in page.findall('.//{*}word'):
        x0,x1,y0,y1=(float(word.attrib[k]) for k in ('xMin','xMax','yMin','yMax'))
        need(0<=x0<=x1<=width and 0<=y0<=y1<=height, 'word outside page');margin=min(margin,x0,y0,width-x1,height-y1);count+=1
need(count>0, 'empty PDF')
for p,h in PINS.items():need(digest(p)==h, 'input changed: '+str(p))
for p,h in receipt['input_sha256_before'].items():need(digest(p)==h, 'captured input changed during audit: '+p)
for n in (1,2):
    b=A/f'build0{n}';result=json.loads((b/'RESULT.json').read_text())
    for name,h in result['input_sha256'].items():need(digest(D.parents[1]/name)==h,'build input changed during audit: '+name)
print(json.dumps({'status':'PASS','graph_rows':len(rows),'live_rows':len(live),'operations':dict(Counter(r[1] for r in rows)),
 'selectors':len(printed),'slots':len(slots),'payload_raw_sha256':payload_hashes,'pdf_pages':4,'bbox_words':count,
 'minimum_word_margin_points':round(margin,3),'tex_sha256':digest(A/'equation.tex'),'pdf_sha256':digest(A/'equation.pdf'),
 'scope':'external source-text, PDF extraction, finite arithmetic and recorded receipt audit; not a Lean proof about a parsed file or an iPRA proof'},indent=2,sort_keys=True))
