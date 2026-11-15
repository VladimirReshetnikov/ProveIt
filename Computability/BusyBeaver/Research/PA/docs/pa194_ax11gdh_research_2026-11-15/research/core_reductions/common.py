from pathlib import Path
import json,sys,hashlib
HERE=Path(__file__).resolve().parent
DATA=HERE/'inputs'
for relative,digest in json.loads((HERE/'input_sha256.json').read_text()).items():
 assert hashlib.sha256((HERE/relative).read_bytes()).hexdigest()==digest
if not __debug__:raise RuntimeError('Run without Python -O.')
sys.path.insert(0,str(HERE))
import symbolic_runtime as s
labels=json.loads((DATA/'labels.json').read_text())
rows={}
for line in (DATA/'primary.tm').read_text().splitlines():
 q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));rows[labels[q],b]=w,d=='R',labels[n]
sites=json.loads((DATA/'sites.json').read_text());ins=json.loads((DATA/'instructions.json').read_text())
contracts=[]
for i,code in enumerate(ins):
 st=s.frame(tuple(map(int,sites[i][0])))
 if code[0]=='inc':
  _,r,n=code;contracts.append((i,None,st,s.canonical(s.frame(tuple(map(int,sites[n][0])),0,('x','inc',s.PHYSICAL[r])))))
 elif code[0]=='dec':
  _,r,z,p=code
  contracts.append((i,(s.PHYSICAL[r],True),st,s.canonical(s.frame(tuple(map(int,sites[z][0]))))))
  contracts.append((i,(s.PHYSICAL[r],False),st,s.canonical(s.frame(tuple(map(int,sites[p][0])),1,('x','dec',s.PHYSICAL[r])))))
 elif code[0]=='jump':contracts.append((i,None,st,s.canonical(s.frame(tuple(map(int,sites[code[1]][0]))))))
 else:contracts.append((i,None,st,None))
