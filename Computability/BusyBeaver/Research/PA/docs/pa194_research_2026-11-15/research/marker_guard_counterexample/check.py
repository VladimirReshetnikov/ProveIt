import json,sys,time
from pathlib import Path
P=Path(__file__).resolve().parents[1]/'physical_searches/primary'
sys.path.insert(0,str(P))
import symbolic_runtime as c
rows={}
for l in (P/'pa194.native.tm').read_text().splitlines():
 q,b,w,d,n=l.split(); rows[int(q),int(b)]=(int(w),d=='R',int(n))
rows={(q,b):(w,d,88 if n==301 else n) for (q,b),(w,d,n) in rows.items() if q!=301}
rows[88,0]=0,False,51;rows[51,0]=0,True,122
rows[122,0]=0,False,174;rows[174,0]=0,True,30
sites=json.loads((P/'sites.json').read_text());ins=json.loads((P/'instructions.json').read_text())
cs=[]
for i,code in enumerate(ins):
 st=c.frame(tuple(map(int,sites[i][0])))
 if code[0]=='inc':
  _,r,n=code;cs.append((i,None,st,c.canonical(c.frame(tuple(map(int,sites[n][0])),0,('x','inc',c.PHYSICAL[r])))))
 elif code[0]=='dec':
  _,r,z,p=code
  cs.append((i,(c.PHYSICAL[r],True),st,c.canonical(c.frame(tuple(map(int,sites[z][0]))))))
  cs.append((i,(c.PHYSICAL[r],False),st,c.canonical(c.frame(tuple(map(int,sites[p][0])),1,('x','dec',c.PHYSICAL[r])))))
 elif code[0]=='jump':cs.append((i,None,st,c.canonical(c.frame(tuple(map(int,sites[code[1]][0]))))))
 else:cs.append((i,None,st,None))
fails=[]
for co in cs:
 if c.run(rows,co) is None:fails.append(co[:2])
print('fails',len(fails),fails,flush=True)
q=74;h=0;ones=set();hist=[]
for t in range(300000):
 b=int(h in ones);w,d,n=rows[q,b]
 if t<130:hist.append((t,q,h,b,w,'R' if d else 'L',n,''.join(str(int(x in ones)) for x in range(h-5,h+6))))
 if q==n and b==0 and (not ones or (h>max(ones) if d else h<min(ones))): print('ray',t,q,h,len(ones));break
 (ones.add if w else ones.discard)(h);h+=1 if d else -1;q=n
 if q==254:print('halt',t+1);break
else: print('limit',q,h,len(ones))
print(*hist,sep='\n')
(Path.cwd()/'guardpatch193.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for(q,b),(w,d,n)in sorted(rows.items())))
