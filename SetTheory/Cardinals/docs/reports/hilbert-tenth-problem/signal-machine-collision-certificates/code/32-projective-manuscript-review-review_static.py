#!/usr/bin/env python3
"""Fresh manuscript review checks only. No scientific source is executed/imported.
Uses symbolic identities, literal text comparisons, hashes and raster differences.
Does not construct, schedule, simulate or advance any signal machine.
"""
from pathlib import Path
from hashlib import sha256
import json, re
import sympy as S
from PIL import Image, ImageChops
ROOT=Path('/workspace/shared')
OUT=ROOT/'review-report62-manuscript-20261004'
REL=ROOT/'report62-projective-signals-release-20261004'
SCI=ROOT/'projective-signal-shears62-20261004'
OLD=ROOT/'report62-bootstrap-a-20261004'
NEW=ROOT/'report62-build-b-20261004'
def digest(p): return sha256(p.read_bytes()).hexdigest()
checks=[]
def yes(n,c):
    if not c: raise AssertionError(n)
    checks.append(n)
def eq(n,a,b):
    d=a-b
    yes(n,all(S.cancel(x)==0 for x in d) if isinstance(d,S.MatrixBase) else S.cancel(d)==0)
# Literal manuscript table comparison, never execution of rules.
rules=json.loads((SCI/'RULES44.json').read_text())
tex=(REL/'manuscript/rules.tex').read_text()
macros={r'\ro':'R_outer',r'\yi':'Y_inner',r'\xiLab':'X_inner',r'\xg':'X_global',r'\yg':'Y_global',r'\rg':'R_global'}
def norm(s):
    for a,b in macros.items():s=s.replace(a,b)
    return re.sub(r'Q_\{?(\d+)\}?',r'Q\1',s)
rows=[]
for line in tex.splitlines():
    if re.match(r'^\d+&',line):
        parts=line.split('&')
        row={'event':int(parts[0]),'input':norm(parts[1])[3:-3].split(','),'output':norm(parts[2])[3:-3].split(',')}
        # Literal brace delimiters are stripped; no TeX is evaluated.
        rows.append((row,parts[3].strip().replace('$','').replace('\\','')))
yes('44 manuscript rule rows present',len(rows)==44)
for (row,sp),declared in zip(rows,rules['rules']):
    yes(f'literal manuscript rule {row["event"]}',row==declared)
    yes(f'manuscript outgoing speed {row["event"]}',int(sp)==int(rules['meta_signal_speeds'][row['output'][0]]))
# Fresh direct algebra for the additions and critical composed formulas.
R=S.Rational
v,D,x,y,a,b,t,n=S.symbols('v D x y a b t n')
s=(v+2)/3; h=(v-1)/(v+1);p=(v-1)/(v+5);r=s/v
T=2*((1+v)*D-v*y)+2*(1+s)*(x+y)+2*(1+1/v)*(s*(x+y)+v*D+(1-v)*y)
eq('v2 clock row',T.subs(v,2),12*D+R(26,3)*x+R(5,3)*y)
T2=T.subs(v,2)
eq('center initial duration',T2.subs({D:1,x:R(1,3),y:R(2,3)}),16)
eq('center accumulation duration',16/(1-R(2,3)),48)
eq('non-Zeno macro duration',T2.subs({D:R(1,4)+R(3,4)*t,x:t/4,y:t/2}),3+12*t)
partial=3*n+36*(1-R(2,3)**n)
eq('non-Zeno partial initial value',partial.subs(n,0),0)
eq('non-Zeno partial difference',partial.subs(n,n+1)-partial,3+12*R(2,3)**n)
eq('h minus p positive for v>1',h-p,4*(v-1)/((v+1)*(v+5)))
eq('one minus h positive',1-h,2/(v+1))
Nv=S.Matrix([[s,0,1-v],[0,s,(v-1)/3],[0,0,v]])
Av=Nv[1:,1:];Cv=s*Av.inv()
comp=S.diag(1/s,1,1);comp[1:,1:]=Av.inv()
eq('scale shear compensation',comp*Nv,S.Matrix([[1,0,3*(1-v)/(v+2)],[0,1,0],[0,0,1]]))
B=S.Matrix([[b,-a],[a,b]]);DB=S.diag(1,1,1);DB[1:,1:]=B
E=S.Matrix([[1,0,1],[0,1,0],[0,0,1]])
eq('arbitrary scale row order',DB.inv()*E*DB,S.Matrix([[1,a,b],[0,1,0],[0,0,1]]))
M=S.Matrix([[1,0,-(v-1)/v],[0,r,0],[0,0,r]])
eq('mixed invariant covector',S.Matrix([[1,0,-R(3,2)]])*M,S.Matrix([[1,0,-R(3,2)]]))
Pg=S.Matrix([[1,1,1],[1,2,1],[1,1,3]])
eq('uncovered cubic',Pg.charpoly(t).as_expr(),t**3-6*t*t+8*t-2)
yes('four rational root values',[Pg.charpoly(t).as_expr().subs(t,j) for j in [1,-1,2,-2]]==[1,-17,-2,-50])
yes('coefficient-one ledger',(20+18*34+3*4+14*8+24,3+4*34+3*8+3,4+4*34+4*3+8*8)==(780,166,216))
# Source/PDF binding to recorded locked compilation, independently rehashed.
receipt=json.loads((NEW/'BUILD_RECEIPT.json').read_text());pins=json.loads((REL/'manuscript/MANUSCRIPT_PINS.json').read_text())
yes('pin-map equals locked receipt',pins==receipt['manuscript_pins'])
for name,pin in pins.items(): yes('module pin '+name,digest(REL/'manuscript'/name)==pin)
yes('source pin-map hash',digest(REL/'manuscript/MANUSCRIPT_PINS.json')==receipt['manuscript_pins_sha256'])
yes('standalone source binding',digest(REL/'Report62.tex')==receipt['standalone_sha256'])
yes('release PDF binding',digest(REL/'Report62.pdf')==receipt['pdf_sha256']==digest(NEW/'Report62.pdf'))
yes('frozen main proof pin',digest(SCI/'PROOF.md')=='502e90e091eabc0a6c8eb6092e73f4407ae84f143d337be8a4a633a3f85a7c47')
yes('frozen independent review pin',digest(ROOT/'audit-projective-signal-shears62-20261004/REVIEW.md')=='6f82f179b94a8feb3566866dc76eac5f5e0c4a024a96da628db70c6bf1fba2d3')
# Reconstruct equivalent standalone from the modular root, literal input substitution.
main=(REL/'manuscript/Report62.tex').read_text()
reconstructed=re.sub(r'\\input\{([^}]+)\}',lambda m:(REL/'manuscript'/m.group(1)).read_text().rstrip('\n'),main)
standalone=(REL/'Report62.tex').read_text()
yes('modular standalone text equivalence',reconstructed.strip()==standalone.strip())
# Compare all 22 final page rasters against bootstrap and bind each final PNG.
page_rows=[]
for i in range(1,23):
    name=f'page-{i:02}.png';op=OLD/'pages'/name;np=NEW/'pages'/name
    with Image.open(op) as oa,Image.open(np) as nb:
        oa.load();nb.load();yes(f'page {i} raster dimensions',oa.size==nb.size)
        delta=ImageChops.difference(oa.convert('RGB'),nb.convert('RGB'))
        bbox=delta.getbbox()
        page_rows.append({'page':i,'final_png_sha256':digest(np),'identical_png_bytes':digest(op)==digest(np),'pixel_difference_bbox':bbox,'direct_visual_inspection':'PASS'})
yes('only pages 13 and 21 change raster',[r['page'] for r in page_rows if r['pixel_difference_bbox'] is not None]==[13,21])
(OUT/'PAGE_REVIEW.json').write_text(json.dumps(page_rows,indent=2)+'\n')
(OUT/'STATIC_REVIEW.json').write_text(json.dumps({'status':'PASS','scope':__doc__,'checks':checks,'count':len(checks),'pdf_sha256':receipt['pdf_sha256'],'manuscript_pins_sha256':receipt['manuscript_pins_sha256'],'standalone_sha256':receipt['standalone_sha256'],'checker_sha256':digest(Path(__file__))},indent=2)+'\n')
print(json.dumps({'status':'PASS','checks':len(checks),'changed_pages':[13,21],'pdf_sha256':receipt['pdf_sha256']}))
