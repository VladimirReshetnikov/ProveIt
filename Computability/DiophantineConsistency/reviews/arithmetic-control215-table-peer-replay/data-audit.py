"""Independent inert reconstruction of the actual p215 rows; no source writes."""
from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
B=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def record(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
program=B/'KSource215Program.lean';main=B/'ArithmeticControl215Table.lean'
require(record(program)['sha256']=='7ab40d3faf9ddb976cdac2f77727e9e43b99b13a81fb45a340ad99abdfcd8310','program pin')
require(record(main)['sha256']=='124d6a19e02d8ac41cfc2fe859b142d015995db623f6ef073bd37ef72396d8a5','main pin')
text=program.read_text();nodes={}
for number,row in re.findall(r'^  \| (\d+) => (.*)$',text,re.M):
 edges=[]
 for op,val in re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',row):edges.append((op,int(val) if val else 0))
 require(len(edges)==2,'two edges');nodes[int(number)]=edges
require(list(nodes)==list(range(179)),'complete node indices')
require('def p215 : Program := ⟨p215Nodes, 178, 179⟩' in text,'actual root and fuel')
require('def t215 : Tree := ptree p215' in text,'actual tree')
for n,edges in nodes.items():
 for op,val in edges:
  if op=='node':require(val<n,'acyclic decreasing nodes')
leaves=[]
def expand(n,prefix):
 for bit,(op,val) in enumerate(nodes[n]):
  path=prefix+(bit,)
  if op=='node':expand(val,path)
  else:leaves.append((path,(op,val)))
expand(178,());require(len(leaves)==4751,'all leaves')
index={p:i+1 for i,(p,e) in enumerate(leaves)};require(len(index)==4751,'unique consumed paths')
def control(path):
 n=178;consumed=();i=0
 while True:
  require(i<180,'actual decoder fuel')
  bit=path[i] if i<len(path) else 0
  consumed+=(bit,);op,val=nodes[n][bit];i+=1
  if op!='node':return index[consumed]
  n=val
def inc(path):
 value=int(''.join(map(str,path)) or '0',2)
 return tuple(((value+1)>>(len(path)-1-i))&1 for i in range(len(path)))
def strip(path,bit,k):
 hits=[i for i in range(len(path)-1,-1,-1) if path[i]==bit]
 return path if k==0 else path[:hits[k-1]] if k<=len(hits) else ()
frame=B/'Permutation252Frame.lean'
part=frame.read_text().split('def physOf : Nat → Nat',1)[1].split('/--',1)[0]
phys={int(i):int(j) for i,j in re.findall(r'\| (\d+) => (\d+)',part)}
require(list(phys)==list(range(9)),'nine physical indices')
rows=[]
for path,(op,v) in leaves:
 if op=='halt':row=[4,0,0,0]
 elif op=='inc':dest=control(inc(path));row=[1,phys[v],dest,dest]
 elif op=='decnz':row=[2,phys[v],control(inc(strip(path,0,1))),control(inc(path))]
 elif op=='brk':dest=control(inc(strip(path,0,v)));row=[3,0,dest,dest]
 elif op=='cont':dest=control(strip(path,1,v));row=[3,0,dest,dest]
 else:raise RuntimeError('unrecognized terminal')
 rows.append(row)
s=main.read_text();literal=re.findall(r'def packed215 : Nat := 0x([0-9a-f]+)',s)
require(len(literal)==1,'one complete literal');packed=int(literal[0],16)
decoded=[];repacked=0
for i,row in enumerate(rows):
 slot=(packed>>(36*i))&((1<<36)-1)
 decoded.append([slot%8,((slot>>3)%16)%9,(slot>>7)%8192,(slot>>20)%8192])
 op,reg,q0,q1=row;require(op<8 and reg<9 and q0<8192 and q1<8192,'slot ranges')
 repacked+=(op+(reg<<3)+(q0<<7)+(q1<<20))<<(36*i)
require(decoded==rows,'all actual row slots');require(packed==repacked,'exact literal incl reserved/high bits')
require(packed<(1<<(36*4751)),'whole high bits')
require([int(i) for i in re.findall(r'private theorem block_(\d+) : block',s)]==list(range(75)),'75 block declarations')
require([int(i) for i in re.findall(r'Fin.cases block_(\d+)',s)]==list(range(75)),'75 block proofs wired once')
require(rows[0]==[2,1,3,2],'first instruction')
result={'status':'PASS','scope':'Independent complete literal data reconstruction; Lean kernel proof remains the logical binding.',
 'sources':[record(program),record(main),record(frame)],'nodes':179,'leaves':len(rows),'rows_sha256':hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
 'physical_map':[phys[i] for i in range(9)],'hex_digits':len(literal[0]),'hex_sha256':hashlib.sha256(literal[0].encode()).hexdigest(),'packed_bits':packed.bit_length(),
 'all_rows_equal':True,'repacked_equal':True,'blocks':75,'last_block_rows':4751%64,'first_row':rows[0],
 'max_leaf_depth':max(len(p) for p,e in leaves),'script':record(Path(__file__))}
Path('/tmp/control215-table-peer-data.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
