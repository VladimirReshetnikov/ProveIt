"""Independent indexed-BFS943 numeral and literal straight-line-program audit.
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
parent=root/'inherited/strict/upstream_lucas/parent'
recipe=parent/'rebuild_coefficients.py'
tree=ast.parse(recipe.read_text())
literals={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('CODE','ALPHABET')}
code=literals['CODE'];alphabet=literals['ALPHABET']
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
# Radix-2^67 column collection: first collect finite sparse coefficient maps,
# then evaluate each independently at the literal radix.
K=Counter({e:1 for e in (30,62,1100,2201,8849)})
for i,(w,n,e,s) in sorted(tiles.items()):
 value=w+256*n+(1<<17)*e+(1<<25)*s+(127<<34)
 c=1+(1<<51)-(value<<10)
 for end in (4393,5495):K[end-i]+=c
for bit,base,length in [(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]:
 for offset in range(length):
  for end in (4393,5495):K[end-base-offset]+=1<<(bit+offset)
value=lambda p:sum(c<<(67*e) for e,c in p.items())
beta=(1<<(67*8807))-1
support=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
MC=beta-value({e:1 for e in support if e!=1})-(2<<(67*1063))
F=Counter({0:4,4393:(1<<51)-2,5495:(1<<51)-2,2195:1,3296:1,8805:(1<<19)-1})
F.update({e:1 for e in range(1013,1023)});F.update({e:1 for e in range(1065,1074)});F.update({e:(1<<65)-1 for e in range(8792,8805)})
ports={'beta':beta,'K0':value(K),'MC':MC,'MF':beta+value(F)}
expected={'beta':'0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d','K0':'0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f','MC':'6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4','MF':'48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737'}
records=[]
for path in sorted(root.glob('positive10_degree*_ops*.json')):
 g=json.loads(path.read_text());need(g['domain']=='strictly positive integers' and len(g['witnesses'])==10,'strict ten-positive domain')
 need(set(g['fixed_numerals'])==set(ports),'four fixed ports')
 pins=g['coefficient_binding'];need(set(pins['ports'])==set(ports),'complete numeral binding')
 for name,meta in pins['ports'].items():
  compressed=(root/pins['path']/meta['file']).read_bytes();raw=gzip.decompress(compressed)
  need(sha(compressed)==meta['gzip_sha256'] and sha(raw)==expected[name]==meta['raw_sha256'],'numeral compressed/raw hashes')
  need(int.from_bytes(raw,'little')==ports[name] and ports[name].bit_length()==meta['bits'],'independently reconstructed whole numeral')
  need(ports[name].to_bytes((ports[name].bit_length()+7)//8,'little')==raw,'minimal literal encoding')
 available=set(g['witnesses'])|set(ports);initial=available.copy();defs={};counts=Counter()
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
 need(live==available,'all registers, variables, and numeral ports live')
 need(sum(counts.values())==g['operations'] and dict(counts)==g['operation_breakdown'],'measured binary operation count')
 records.append({'path':path.name,'variables':len(g['witnesses']),'operations':sum(counts.values()),'operation_breakdown':dict(counts),'all_live':True,'sha256':sha(path.read_bytes())})
need(records,'at least one positive-ten arithmetic graph')
print(json.dumps({'status':'PASS','machine_code_sha256':sha(code.encode()),'machine_actions':len(actions),'indexed_tiles':len(tiles),'literal_corrected_initializer':list(tiles[929]),'four_numerals_independently_reconstructed':True,'ports':[{'name':k,'bits':v.bit_length(),'raw_sha256':expected[k]}for k,v in ports.items()],'circuits':records,'boundary':'Finite whole-tuple numeral reconstruction and literal DAG/liveness/operation metrics; exact-degree and unbounded solvability proofs are separate checks.'},indent=2))
