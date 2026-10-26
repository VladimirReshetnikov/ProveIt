"""Independent Start4127 numeral and literal straight-line-program audit.
No producer/verifier imports or evaluation of source code. The packed machine
literal is parsed as a constant and bound to the final pinned source recipe.
"""
import ast
from collections import Counter
import gzip, hashlib, json
from pathlib import Path
import sys
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release/scalar/positive10')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
recipe=root/'native4127/start_only.py'
tree=ast.parse(recipe.read_text())
literals={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('SEED','ALPHABET')}
code=literals['SEED'];alphabet=literals['ALPHABET']
need(len(code)==436 and alphabet=='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz','finite encoded machine literal')
packed=sum(alphabet.index(c)*62**k for k,c in enumerate(code[::-1]))
nu_bits=packed & ((1<<636)-1)
targets=(packed>>636)&((1<<1675)-1)
exceptions=packed>>2311
seen_new=0;exception_count=0;actions=[]
for state in range(215):
 exceptional=(nu_bits>>(430+state))&1
 instruction=(exceptions>>(4*exception_count))&15 if exceptional else 14
 exception_count+=exceptional
 for bit in (0,1):
  j=2*state+bit;is_new=(nu_bits>>j)&1
  target=1+seen_new if is_new else (targets//216**(j-seen_new))%216
  write=(instruction>>(2*bit))&1;right=(instruction>>(2*bit+1))&1
  actions.append((state,bit,target,write,right));seen_new+=is_new
right_targets=sorted({t for _,_,t,_,d in actions if d});left_targets=sorted({t for _,_,t,_,d in actions if not d})
need(len(actions)==430 and (len(right_targets),len(left_targets))==(199,45),'machine action and signal counts')
right_code={t:j+6 for j,t in enumerate(right_targets)};left_code={t:j+205 for j,t in enumerate(left_targets)}
head=lambda q,b:2*q+2+b
tiles={0:(2,435,3,1),1:(5,0,0,0)}
def put(i,t):
 need(type(i) is int and i not in tiles and len(t)==4,'unique tile index')
 tiles[i]=t
for q,b,t,w,d in actions:put(2+2*q+b,(0,head(q,b),right_code[t],w) if d else (left_code[t],head(q,b),0,w))
for b in (0,1):
 put(432+b,(0,head(215,b),0,head(215,b)));put(434+b,(0,b,0,b))
for q,s in right_code.items():
 for b in (0,1):put(424+2*s+b,(s,b,0,head(q,b)))
for q,s in left_code.items():
 for b in (0,1):put(424+2*s+b,(0,b,s,head(q,b)))
for i,label in enumerate([0,1,432,433]):put(924+i,(0,label,0,438))
for i,t in enumerate([(2,434,2,0),(3,436,4,4),(4,436,4,0),(1,438,1,434),(1,438,1,435),(1,438,1,436)]):put(928+i,t)
for i,(a,b) in enumerate((a,b) for a in (0,1,4) for b in (0,1,2)):put(934+i,(a,437,b,437))
need(set(tiles)==set(range(943)),'whole indexed tile system')
# Recollect the new complemented tuple from independently decoded tiles.
coeff=[0]*3297
for i,(w,n,e,s) in tiles.items():coeff[i]=1+1024*(1+w+256*n+(1<<17)*e+(1<<25)*s)
for start,bit,count in [(943,35,9),(973,18,9),(992,27,8),(1002,10,8)]:
 for k in range(count):coeff[start+k]=1<<(bit+k)
need(coeff==json.loads((root/'native4127/start_only_coefficients.json').read_text()),'all3297 literal complemented weights')
E=set(range(943))|set(range(943,952))|set(range(973,982))|set(range(992,1000))|set(range(1002,1010))|{990,991,1031}
need(len(E)==980 and sum(bool(v) for v in coeff)==977,'physical and weighted support')
p=lambda e:1<<(47*e)
beta=p(4127)-1
K=p(20)+p(30)+p(1031)+p(4137)+sum(v*(p(2042-i)+p(3074-i)) for i,v in enumerate(coeff) if v)
MC=beta-sum(p(i) for i in E if i!=1)-2*p(990)
MF=beta+4+((1<<44)-2)*(p(2042)+p(3074))+sum(p(i) for i in range(973,982))+sum(p(i) for i in range(1012,1020))+p(1031)+(1<<29)*p(4124)-p(4106)
ports={'beta':beta,'K0':K,'MC':MC,'MF':MF}
records=[]
for path in sorted(root.glob('start4127_positive10_degree*_ops*.json')):
 g=json.loads(path.read_text());need(g['domain']=='strictly positive integers' and len(g['witnesses'])==10,'strict ten-positive domain')
 need(set(g['fixed_numerals'])==set(ports),'four fixed ports')
 pins=g['coefficient_binding'];need(set(pins['ports'])==set(ports) and pins['byte_order']=='big','whole big-endian tuple binding')
 for name,meta in pins['ports'].items():
  raw=(root/pins['path']/meta['file']).read_bytes()
  need(sha(raw)==meta['sha256'] and len(raw)==meta['bytes'],'actual coefficient bytes/hash')
  need(int.from_bytes(raw,'big')==ports[name] and ports[name].bit_length()==meta['bits'],'independently reconstructed whole numeral')
  need(ports[name].to_bytes((ports[name].bit_length()+7)//8,'big')==raw,'minimal literal encoding')
 available=set(g['witnesses'])|set(ports);defs={};counts=Counter()
 for row in g['source']:
  need(type(row) is list and len(row)==4,'literal binary register')
  name,op,a,b=row
  need(type(name) is str and name not in available and op in ('+','-','*'),'fresh arithmetic register')
  need(all(type(v) is int or type(v) is str and v in available for v in (a,b)),'strict earlier operand')
  defs[name]=(a,b);available.add(name);counts[op]+=1
 stack=[g['output']];live=set()
 while stack:
  name=stack.pop()
  if type(name) is int or name in live:continue
  need(name in available,'bound output');live.add(name)
  if name in defs:stack.extend(defs[name])
 need(live==available,'all gates witnesses and ports live')
 need(sum(counts.values())==g['operations'] and dict(counts)==g['operation_breakdown'],'measured binary operation count')
 old=json.loads((root/'round21_graphs'/path.name.removeprefix('start4127_')).read_text())
 need(all(old[k]==g[k] for k in ('source','output','witnesses','fixed_numerals','operations','operation_breakdown')),'unchanged graph and witnesses fromR21')
 records.append({'path':path.name,'variables':len(g['witnesses']),'operations':sum(counts.values()),'operation_breakdown':dict(counts),'all_live':True,'sha256':sha(path.read_bytes())})
need(len(records)==3,'three positive-ten graphs')
print(json.dumps({'status':'PASS','seed_sha256':sha(code.encode()),'machine_actions':len(actions),'indexed_tiles':len(tiles),'physical_support':len(E),'all3297_weights_equal':True,'four_numerals_reconstructed_from_seed':True,'raw_tuple_bytes':sum((v.bit_length()+7)//8 for v in ports.values()),'ports':[{'name':k,'bits':v.bit_length(),'raw_sha256':sha(v.to_bytes((v.bit_length()+7)//8,'big'))}for k,v in ports.items()],'circuits':records,'boundary':'Finite whole-tuple reconstruction, literal DAG metrics/liveness and exact unchanged graph; unbounded source calibration proved separately.'},indent=2))
