from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).parent))
import symbolic_runtime as sr
BASE=Path(__file__).parent

def parse(path):
 rows={}
 for line in Path(path).read_text().splitlines():
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
 return rows

def contracts():
 sites=json.loads((BASE/'pa194.sites.json').read_text());ins=json.loads((BASE/'pa194.instructions.json').read_text());out=[]
 for i,code in enumerate(ins):
  st=sr.frame(tuple(map(int,sites[i][0])))
  def frm(n,extra=0,effect=sr.PLAIN):return sr.canonical(sr.frame(tuple(map(int,sites[n][0])),extra,effect))
  if code[0]=='inc':
   _,r,n=code;out.append((i,None,st,frm(n,0,('x','inc',sr.PHYSICAL[r]))))
  elif code[0]=='dec':
   _,r,z,p=code;out.append((i,(sr.PHYSICAL[r],True),st,frm(z)));out.append((i,(sr.PHYSICAL[r],False),st,frm(p,1,('x','dec',sr.PHYSICAL[r]))))
  elif code[0]=='jump':out.append((i,None,st,frm(code[1])))
  else:out.append((i,None,st,None))
 return out

if __name__=='__main__':
 rows=parse(BASE/'pa194.native.tm');cs=contracts();used=set();contexts={}
 def observe(s):
  q,onl,l,r=s
  seg=l if onl else r
  b=sr.headbit(seg)
  used.add((q,b));contexts.setdefault((q,b),[]).append(s)
 print(sr.validate(rows,cs,observe=observe));print('unvisited',sorted(set(rows)-used));print('states',len(set(q for q,b in rows)))
 (BASE/'unused.json').write_text(json.dumps(sorted(set(rows)-used)))
