"""Independent literal replay and optional installation of a SAT detector."""
import sys,json,pathlib,hashlib
p=pathlib.Path(sys.argv[1]);d=json.loads(p.read_text());assert d['sat'];n=d['states'];labels=d['labels'];tab={(q,b):(w,m,s)for q,b,w,m,s in d['table']};S=labels.index(4);long=labels.index(84);out=[]
for i,c in enumerate(d['cases']):
 k=c['k'];ones=set(c['ones']);original=ones.copy();q=h=0;trace=[]
 for tick in range(d['steps']+1):
  shortgoal=k<8 and q==S and h==-k-1
  longgoal=k==8 and q==long and -8<=h<=1
  if (shortgoal or longgoal) and ones==original:
   break
  assert tick<d['steps'],(i,'fuel')
  assert c['lo']<=h<=c['hi'],(i,'read exterior',q,h)
  assert labels[q]!='BAD',(i,'BAD state')
  b=int(h in ones);w,m,s=tab[q,b];trace.append([q,h,b,w,m,s])
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if m=='R'else-1;q=s
 out.append({'case':i,'steps':tick,'state':labels[q],'head':h,'trace':trace})
result={'status':'PASS','source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'case_count':len(out),'maximum_steps':max(r['steps']for r in out),'cases':out}
p.with_suffix('.replay.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k!='cases'})
if '--install' in sys.argv:
 root=pathlib.Path(__file__).resolve().parent;table={}
 for line in(root/'recovered/63/machine/zfc_prefix246_old.tm').read_text().splitlines():
  if line.startswith('#'):continue
  q,b,w,m,s=line.split();table[int(q),int(b)]=(int(w),m,int(s))
 for old in [6,9,13,19,29,41,58,74][n:]:
  for b in(0,1):del table[old,b]
 for q in range(n):
  for b in(0,1):
   w,m,s=tab[q,b];dest=labels[s]
   if dest=='BAD':dest=4
   table[labels[q],b]=(w,m,dest)
 text='#! start 95\n'+''.join(f'{q} {b} {w} {m} {s}\n'for(q,b),(w,m,s)in sorted(table.items()))
 p.with_suffix('.tm').write_text(text);print('Installed',len(table)//2,'states',hashlib.sha256(text.encode()).hexdigest())
