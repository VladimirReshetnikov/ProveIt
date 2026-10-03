#!/usr/bin/env python3
"""Deterministic vector figure directly from every raw occupied-site trace row.
Python standard library only. No source-level model or inferred interpolation.
"""
import hashlib,json,math,pathlib,sys
BASE=pathlib.Path(__file__).resolve().parents[1]
src=BASE/'compiler'/'sample-orbit.json'
obj=json.loads(src.read_text()); rows=obj['states']
W,H=540,590
pdf=[];svg=[]
def color(c): return tuple(int(c[i:i+2],16)/255 for i in (1,3,5))
def line(x1,y1,x2,y2,c='#9299A5',width=.5):
    r,g,b=color(c);pdf.append(f'{r:.4f} {g:.4f} {b:.4f} RG {width:.2f} w {x1:.2f} {H-y1:.2f} m {x2:.2f} {H-y2:.2f} l S')
    svg.append(f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" y2="{y2:.2f}" stroke="{c}" stroke-width="{width}"/>')
def text(x,y,s,size=9,c='#26354A'):
    r,g,b=color(c); escaped=s.replace('\\','\\\\').replace('(','\\(').replace(')','\\)')
    pdf.append(f'BT /F1 {size} Tf {r:.4f} {g:.4f} {b:.4f} rg {x:.2f} {H-y:.2f} Td ({escaped}) Tj ET')
    import html
    svg.append(f'<text x="{x:.2f}" y="{y:.2f}" font-family="Courier,monospace" font-size="{size}" fill="{c}">{html.escape(s)}</text>')
def point(x,y,size,c):
    r,g,b=color(c);pdf.append(f'{r:.4f} {g:.4f} {b:.4f} rg {x-size/2:.2f} {H-y-size/2:.2f} {size:.2f} {size:.2f} re f')
    svg.append(f'<rect x="{x-size/2:.2f}" y="{y-size/2:.2f}" width="{size}" height="{size}" fill="{c}"/>')
def panel(x,y,w,h,tmin,tmax,pmin,pmax,xticks,yticks,title,detail=False):
    text(x,y-14,title,11)
    X=lambda t:x+(t-tmin)/(tmax-tmin)*w
    Y=lambda p:y+h-(p-pmin)/(pmax-pmin)*h
    for p in yticks:
        line(x,Y(p),x+w,Y(p),'#E6E9ED');text(x-32,Y(p)+3,str(p),8)
    for t in xticks:
        line(X(t),y,X(t),y+h,'#E6E9ED');text(X(t)-7,y+h+14,str(t),8)
    for row in rows:
        t=row['t']
        if tmin<=t<=tmax:
            for p in row['ones']:
                if pmin<=p<=pmax:
                    c='#B84536' if row['phase']=='-' else '#2167A4'
                    point(X(t),Y(p),2.4 if detail else .70,c)
    line(x,y+h,x+w,y+h);line(x,y,x,y+h)
    text(x+w/2-22,y+h+29,'CA time t',8)
text(20,24,'A complete reversible five-particle accepting orbit',12)
text(20,41,'Each mark is an occupied site from the exact raw trace; blue + phase, red - phase',8)
panel(55,76,460,280,0,1394,-415,415,[0,348,696,1045,1394],[-382,-200,0,200,382],'Full cycle: first halt at 696; return after 1394 steps')
panel(55,425,208,118,-.5,4.5,-25,30,[0,1,2,3,4],[-18,0,18],'Dispatch detail',True)
panel(330,425,185,118,692,701,16,28,[692,696,700],[18,21,25],'Halt and sign-reflection detail',True)
text(20,584,'Data: sample-orbit.json | exactly five ones in each frame | no particle labels or extra track',8)
out=BASE/'figures';out.mkdir(exist_ok=True)
(out/'accepting-orbit.svg').write_text(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}">\n'+ '\n'.join(svg)+'\n</svg>\n')
content=('\n'.join(pdf)+'\n').encode('ascii')
objs=[b'<< /Type /Catalog /Pages 2 0 R >>',b'<< /Type /Pages /Kids [3 0 R] /Count 1 >>',f'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {W} {H}] /Resources << /Font << /F1 4 0 R >> >> /Contents 5 0 R >>'.encode(),b'<< /Type /Font /Subtype /Type1 /BaseFont /Courier >>',f'<< /Length {len(content)} >>\nstream\n'.encode()+content+b'endstream']
buf=bytearray(b'%PDF-1.4\n%vector trace\n'); offsets=[0]
for i,o in enumerate(objs,1):offsets.append(len(buf));buf.extend(f'{i} 0 obj\n'.encode()+o+b'\nendobj\n')
start=len(buf);buf.extend(f'xref\n0 {len(objs)+1}\n0000000000 65535 f \n'.encode())
for off in offsets[1:]:buf.extend(f'{off:010d} 00000 n \n'.encode())
buf.extend(f'trailer\n<< /Size {len(objs)+1} /Root 1 0 R >>\nstartxref\n{start}\n%%EOF\n'.encode())
(out/'accepting-orbit.pdf').write_bytes(buf)
print(json.dumps(dict(status='passed',trace_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),frames=len(rows),raw_points=sum(len(r['ones']) for r in rows),pdf_sha256=hashlib.sha256(buf).hexdigest()),sort_keys=True))
