from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
def require(x,m):
 if not x:raise RuntimeError(m)
def rec(p):return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
def packed(source,name):
 s=source.read_text();m=re.findall(r'^def '+name+r' : Nat := 0x([0-9a-f]+)$',s,re.M)
 require(len(m)==1,'literal '+name);return int(m[0],16),m[0],s
A,_,_=packed(B/'ArithmeticDagControlPerm222.lean','packedRows')
C,_,_=packed(B/'ArithmeticControl215Table.lean','packed215')
P,hexdata,text=packed(B/'ArithmeticControlBisimPerm215.lean','packedCert')
def table(n):
 out=[];raw=n
 for _ in range(4751):
  slot=raw&((1<<36)-1);raw>>=36
  row=(slot&7,(slot>>3)&15,(slot>>7)&8191,(slot>>20)&8191)
  require(row[1]<9 and slot==row[0]+(row[1]<<3)+(row[2]<<7)+(row[3]<<20),'all row bits')
  out.append(row)
 require(raw==0,'no high row bits');return out
ra,rb=table(A),table(C)
entries=[];remaining=P
for _ in range(2850):
 slot=remaining&((1<<96)-1);remaining>>=96
 a=slot&8191;b=(slot>>13)&8191
 alpha=[(slot>>(26+2*k))&3 for k in range(9)]
 beta=[(slot>>(44+2*k))&3 for k in range(9)]
 s0=(slot>>62)&4095;s1=(slot>>74)&4095
 require(slot<1<<86 and a==b and alpha==beta==[0]*9,'entire shape/reserved bits')
 require(0<a<=4751 and s0<2850 and s1<2850,'all entry ranges')
 entries.append([a,b,alpha,beta,s0,s1])
require(remaining==0 and P<1<<(96*2850),'whole high bits')
require(entries[0]==[1,1,[0]*9,[0]*9,2,1],'actual root')
repacked=0
for i,(a,b,al,be,s0,s1) in enumerate(entries):
 slot=a+(b<<13)+sum(v<<(26+2*k) for k,v in enumerate(al))+sum(v<<(44+2*k) for k,v in enumerate(be))+(s0<<62)+(s1<<74)
 repacked+=slot<<(96*i)
require(P==repacked,'complete repack')
def segment(rows,c,offset):
 offset=list(offset)
 for ticks in range(6):
  require(1<=c<=len(rows),'actual segment control')
  row=rows[c-1];op,reg,n0,n1=row
  if op in [2,4]:return row,offset,ticks+1
  if op==1:offset[reg]+=1;c=n0
  elif op==3:c=n0
  else:raise RuntimeError('segment opcode')
 raise RuntimeError('insufficient segment fuel')
halted=tested=0;costs=[]
for i,(a,b,al,be,s0,s1) in enumerate(entries):
 rowa,ua,ca=segment(ra,a,al);rowb,ub,cb=segment(rb,b,be);costs.append((ca,cb))
 if rowa[0]==rowb[0]==4:halted+=1;continue
 require(rowa[0]==rowb[0]==2 and rowa[1]==rowb[1],'same actual test '+str(i))
 require(ua[rowa[1]]==ub[rowb[1]],'same tested offset '+str(i))
 na=[max(x-y,0) for x,y in zip(ua,ub)];nb=[max(y-x,0) for x,y in zip(ua,ub)]
 for successor,branch in [(s0,2),(s1,3)]:
  e=entries[successor]
  require(e[:4]==[rowa[branch],rowb[branch],na,nb],'complete successor '+str(i))
 tested+=1
require([int(k) for k in re.findall(r'private theorem block_(\d+) : block',text)]==list(range(45)),'all block declarations')
require([int(k) for k in re.findall(r'Fin.cases block_(\d+)',text)]==list(range(45)),'all block wiring')
h=hashlib.sha256(json.dumps(entries,separators=(',',':')).encode()).hexdigest()
require(h=='22677a305a6889a1d731f1d78467314bca4ae1f9a889705fffed70d61065b6db','full candidate identity')
result=dict(status='PASS',scope='Independent complete literal/certificate/segment audit; Lean kernel proof supplies logical binding',entries=len(entries),fuel=6,blocks=45,final_block_entries=34,tests=tested,halts=halted,max_cost_A=max(x[0] for x in costs),max_cost_B=max(x[1] for x in costs),hex_digits=len(hexdata),bits=P.bit_length(),hex_sha256=hashlib.sha256(hexdata.encode()).hexdigest(),entry_sha256=h,rows_differ=sum(a!=b for a,b in zip(ra,rb)),sources=[rec(B/n) for n in ['ArithmeticDagControlPerm222.lean','ArithmeticControl215Table.lean','ArithmeticControlBisimPerm215.lean']],script=rec(Path(__file__)))
Path('/tmp/control-bisim-perm215-root-data.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
