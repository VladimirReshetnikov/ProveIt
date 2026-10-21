"""Owned read-only literal native/Lean transition-table equality checker."""
import re,json,pathlib,hashlib
O=pathlib.Path(__file__).resolve().parent
s=(O/'KTable215.lean').read_text()
core=s.split('def table215 : List (Row × Row) := [',1)[1].split('def tm215',1)[0]
rows=[]
for line in core.splitlines():
 if not line.strip() or line.strip()==']':continue
 row=re.findall(r'some \((true|false), (true|false), (\d+)\)|\b(none)\b',line)
 assert len(row)==2,(line,row)
 rows.append(row)
formal={(q,r):(int(w=='true'),'R' if d=='true' else 'L',int(n))for q,row in enumerate(rows)for r,(w,d,n,none)in enumerate(row)if not none}
native={}
for line in (O/'k215.native.tm').read_text().splitlines():
 if not line.strip() or line.startswith('#'):continue
 q,r,w,d,n=line.split();native[int(q),int(r)]=int(w),d,int(n)
rename=lambda q:{254:230,301:102,302:120}.get(q,q)
transported={(rename(q),r):(w,d,rename(n))for(q,r),(w,d,n)in native.items()}
assert len(native)==len(formal)==430
assert transported==formal
print('PASS: all430 rows equal under254→230,301→102,302→120.')
