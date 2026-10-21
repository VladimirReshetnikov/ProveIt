"""Finite primitive-interface screening data; never an unbounded proof."""
from pathlib import Path
import argparse,json,hashlib
PACKET=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=PACKET/'data/sites218.json')
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();P=args.output;P.mkdir(parents=True,exist_ok=True)
source=args.source
S=json.loads(source.read_text());PHY=[6,2,0,4,3,7,8,5,1]
def frame(pc,regs,spares,gap):
 physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=regs[i]
 out={-1,64+gap}|{i for i,c in enumerate(pc)if c=='1'};p=65+gap
 for n in physical+spares:
  p+=1;out.update(range(p,p+n+1));p+=n+1
 return out
def inc(pc):
 n=len(pc);v=(int(pc,2)if pc else 0)+1
 return (format(v%2**n,'0'+str(n)+'b')if n else ''),int(v==2**n)
def strip(pc,bit,k):
 for i in range(len(pc)-1,-1,-1):
  if pc[i]==bit:
   k-=1
   if not k:return pc[:i]
 return ''
rows=[];metadata=[]
for trial in range(2):
 for index,(pc,op,arg)in enumerate(S):
  for positive in ([False,True]if op=='CD'else[False]):
   regs=([0]*9 if trial==0 else [i%3 for i in range(9)]);spares=([0]if trial==0 else[2,0,1]);gap=0 if trial==0 else 3
   if op=='CD':regs[arg]=(1+trial if positive else 0)
   initial=frame(pc,regs,spares,gap);rr=regs.copy();ss=spares.copy();delta=shift=0
   if op=='CH':targetq=254;targeth=0;target=set()
   else:
    if op=='CI':rr[arg]+=1;ss.append(1);nxt,shift=inc(pc)
    elif op=='CD'and positive:rr[arg]-=1;delta=1;nxt,shift=inc(pc)
    elif op in('CD','CB'):nxt,shift=inc(strip(pc,'0',arg if op=='CB'else 1))
    elif op=='CC':nxt=strip(pc,'1',arg)
    else:raise ValueError(op)
    targetq=84;targeth=-shift;target={i-shift for i in frame(nxt,rr,ss,gap+delta+shift)}
   rows.append(' '.join(map(str,[index,int(positive),trial,len(initial),*sorted(initial),targetq,targeth,len(target),*sorted(target)])))
   metadata.append({'index':index,'positive':positive,'trial':trial,'site':[pc,op,arg],'registers':regs,'spares':spares,'gap':gap})
(P/'cases.txt').write_text(str(len(rows))+'\n'+'\n'.join(rows)+'\n')
(P/'case_metadata.json').write_text(json.dumps(metadata,separators=(',',':'))+'\n')
(P/'case_manifest.json').write_text(json.dumps({'cases':len(rows),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'case_file_sha256':hashlib.sha256((P/'cases.txt').read_bytes()).hexdigest(),'scope':'Two finite assignments at every source occurrence and decrement guard; screening only.'},indent=2)+'\n')
print('prepared',len(rows),'cases')
(P/'source.txt').write_text(str(len(S))+'\n'+''.join(f'{pc} {op} {-1 if arg is None else arg}\n'for pc,op,arg in S))
