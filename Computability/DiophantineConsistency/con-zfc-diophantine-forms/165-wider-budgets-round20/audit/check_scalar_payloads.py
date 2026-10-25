"""Independent literal scalar payload/DAG audit, not exact-degree proof."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys

root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release/scalar')
expected={
 'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
 'K0':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
 'MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
 'MF':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
 'cone_A':'66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
 'cone_B':'42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}
def require(ok,message):
 if not ok:raise ValueError(message)
binding=json.loads((root/'coefficients/BINDING.json').read_text())
require(set(binding['payloads'])==set(expected),'six fixed numeral ports')
ports={};records=[]
for name,pin in binding['payloads'].items():
 raw=gzip.decompress((root/'coefficients'/pin['file']).read_bytes())
 digest=hashlib.sha256(raw).hexdigest()
 require(digest==expected[name]==pin['raw_sha256'],'authentic raw numeral '+name)
 value=int.from_bytes(raw,'little');ports[name]=value
 require(value>0 and value.bit_length()==pin['bits'] and len(raw)==pin['raw_bytes'],'positive numeral length')
 require(value.to_bytes((value.bit_length()+7)//8,'little')==raw,'minimal little-endian encoding')
 records.append({'name':name,'bits':value.bit_length(),'raw_bytes':len(raw),'sha256':digest})
require(ports['beta']==(1<<1064921)-1,'beta recipe')
require(ports['cone_A']==1<<1113 and ports['cone_B']==1<<666104,'cone recipes')
# Independently reconstruct the six literal numerals without importing recipe code.
recipe_dir=root/'coefficients/recipe'
raw_machine=(recipe_dir/'k215.tm').read_bytes()
require(hashlib.sha256(raw_machine).hexdigest()=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090','machine literal identity')
actions=[]
for line in raw_machine.decode().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,m,t=line.split();actions.append((int(q),int(b),int(w),m,int(t)))
require(len(actions)==430 and len({(q,b) for q,b,w,m,t in actions})==430,'complete machine transition list')
right=sorted({t for q,b,w,m,t in actions if m=='R'});left=sorted({t for q,b,w,m,t in actions if m=='L'})
require((len(right),len(left))==(199,45),'machine signal counts')
rs={q:i+6 for i,q in enumerate(right)};ls={q:i+205 for i,q in enumerate(left)}
head=lambda q,b:2*q+2+b
tiles={(0,head(q,b),rs[t],w) if m=='R' else (ls[t],head(q,b),0,w) for q,b,w,m,t in actions}
for b in (0,1):
 tiles.update([(0,head(215,b),0,head(215,b)),(0,b,0,b)])
 tiles.update((rs[q],b,0,head(q,b)) for q in right)
 tiles.update((0,b,ls[q],head(q,b)) for q in left)
tiles.update((0,n,0,438) for n in (0,1,432,433))
tiles.update([(2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0)])
tiles.update((1,438,1,n) for n in (434,435,436))
tiles.update((a,437,b,437) for a in (0,1,4) for b in (0,1,2))
start_tile=(2,435,3,1);bad=(5,0,0,0);tiles.add(bad)
ordered=[start_tile,bad]+sorted(tiles-{start_tile,bad})
require(len(ordered)==943 and [list(t) for t in ordered]==json.loads((recipe_dir/'wang943_tiles.json').read_text()),'independent machine-to-tile reconstruction')
weight=lambda j:1<<(10+2*j)
coeff={i:1+sum(weight(10*k+j) for k,label in enumerate(tile) for j in range(10) if ((label+512)>>j)&1)+sum(weight(j) for j in range(40,44)) for i,tile in enumerate(ordered)}
for k,offset in enumerate((1020,1000,980,960)):
 for j in range(10):coeff[offset+2*j]=weight(10*k+j)
coeff.update({a:weight(40+j) for j,a in enumerate((1095,1096,2195,3296))})
coeff.update({1063:0,1064:0});require(len(coeff)==989,'coefficient support')
dc={e:1 for e in (40,41,1100,2200)}
for e,c in coeff.items():
 for endpoint in (4393,5495):dc[endpoint-e]=dc.get(endpoint-e,0)+c
b=121;B=1<<(121*8801);rho=1<<b
DC=sum(v<<(b*e) for e,v in dc.items())
MC=B-1-sum(1<<(b*e) for e in coeff if e!=1)-(2<<(b*1063))
mu=1022+sum(weight(j) for j in range(44))
MF=4+(mu<<(b*4393))+(mu<<(b*5495))
MF+=sum(1<<(b*(1000+2*j)) for j in range(10))+sum(1<<(b*(1021+2*j)) for j in range(10))
MF+=(1<<(b*2195))+(1<<(b*3296))+sum(((1<<119)-1)<<(b*e) for e in range(8792,8799))+(((1<<27)-1)<<(b*8799))
require(ports=={'beta':B-1,'K0':DC+B*rho,'MC':MC,'MF':MF+B-1,'cone_A':1<<1113,'cone_B':1<<666104},'all six independent finite numeral recipes')
circuits=[]
for p in sorted(root.glob('*.json')):
 obj=json.loads(p.read_text())
 if not isinstance(obj,dict) or obj.get('schema')!='integer-polynomial-dag-v1':continue
 nodes=obj['nodes'];output=obj['output']
 require(type(output) is int and 0<=output<len(nodes),'DAG output')
 require(obj['domain']=='unrestricted integers' and len(obj['variables'])==obj['variable_count']==11,'eleven-integer domain')
 counts=Counter();leaves=Counter();variables=[];coefficients=[]
 for name, idx in obj.get('named_registers',{}).items():
  require(isinstance(name,str) and type(idx) is int and 0 <= idx < len(nodes), 'strict named-register index')
 for i,row in enumerate(nodes):
  op=row[0]
  if op in {'add','sub','mul'}:
   require(len(row)==3 and all(type(x) is int and 0<=x<i for x in row[1:]),'backwards finite DAG edges')
   counts[op]+=1
  else:
   require(len(row)==2 and op in {'variable','coefficient','integer'},'literal arithmetic DAG leaf')
   if op=='integer':require(type(row[1]) is int,'fixed integer literal')
   elif op=='variable':variables.append(row[1])
   else:require(row[1] in ports,'bound coefficient numeral');coefficients.append(row[1])
 require(variables==obj['variables'] and set(coefficients)==set(ports) and len(coefficients)==6,'all fixed variable/numeral leaves')
 reachable=set();stack=[output]
 while stack:
  i=stack.pop()
  if i in reachable:continue
  reachable.add(i)
  if nodes[i][0] in {'add','sub','mul'}:stack.extend(nodes[i][1:])
 require(reachable==set(range(len(nodes))),'all DAG gates live')
 require(dict(counts)==obj['operation_counts'] and sum(counts.values())==obj['operations'],'measured live binary-operation count')
 circuits.append({'path':p.name,'variables':11,'nodes':len(nodes),'binary_operations':sum(counts.values()),
                  'operation_counts':dict(counts),'all_nodes_live':True,'declared_exact_degree_not_reproved_here':obj['exact_degree']})
require(circuits,'at least one literal polynomial DAG')
require(len(circuits)>=1,'at least one released circuit')

print(json.dumps({'status':'PASS','payloads':records,'all_six_independently_reconstructed':True,'machine_actions':len(actions),'independent_tiles':len(ordered),'literal_circuits':circuits,
 'boundary':'Literal numeral identity/encoding and ordinary finite arithmetic DAG structure/counts. All six finite coefficient recipes independently reconstructed from literal machine transitions; exact cancellation degrees require the separate scalar checker.'},indent=2))
