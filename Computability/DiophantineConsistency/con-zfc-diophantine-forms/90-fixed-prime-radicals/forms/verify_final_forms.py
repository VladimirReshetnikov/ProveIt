#!/usr/bin/env python3
"""Finite literal/degree checks. These do not prove the inherited semantic compiler."""
from pathlib import Path
import json,gzip,hashlib,sys,time
PRIME=1000000007
DIGIT_BYTES=16

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b,minus=False):
 out=[0]*max(len(a),len(b))
 for i in range(len(out)):out[i]=((a[i] if i<len(a) else 0)+(-1 if minus else 1)*(b[i] if i<len(b) else 0))%PRIME
 return trim(out)

def mul(a,b):
 if len(a)==1:return trim([a[0]*x%PRIME for x in b])
 if len(b)==1:return trim([b[0]*x%PRIME for x in a])
 if min(len(a),len(b))*(PRIME-1)**2>=1<<(8*DIGIT_BYTES):raise RuntimeError('Kronecker digit bound exceeded')
 ai=int.from_bytes(b''.join(x.to_bytes(DIGIT_BYTES,'little') for x in a),'little')
 bi=int.from_bytes(b''.join(x.to_bytes(DIGIT_BYTES,'little') for x in b),'little')
 length=len(a)+len(b)-1;data=(ai*bi).to_bytes(length*DIGIT_BYTES,'little')
 return trim([int.from_bytes(data[i*DIGIT_BYTES:(i+1)*DIGIT_BYTES],'little')%PRIME for i in range(length)])

def load_constants(directory):
 bind=json.loads((directory/'coefficients/BINDING.json').read_text());out={}
 for name,v in bind['ports'].items():
  data=(directory/'coefficients'/v['file']).read_bytes()
  if hashlib.sha256(data).hexdigest()!=v['sha256_gzip']:raise RuntimeError('compressed binding mismatch: '+name)
  raw=gzip.decompress(data)
  if hashlib.sha256(raw).hexdigest()!=v['sha256_raw']:raise RuntimeError('integer binding mismatch: '+name)
  k=int.from_bytes(raw,'little')
  if k.bit_length()!=v['bits']:raise RuntimeError('bit count mismatch: '+name)
  out[name]=k
 if out['beta']!=2**1064921-1 or out['beta']%3!=1:raise RuntimeError('wrong beta slice')
 if out['cone_A']!=2**1113 or out['cone_B']!=2**666104:raise RuntimeError('wrong determinant scales')
 return out

def evaluate_univariate(packet,constants):
 slopes={v:(i+2)**2+(i+3) for i,v in enumerate(packet['variables'])}
 values={v:[0,x] for v,x in slopes.items()};values.update({n:[k%PRIME] for n,k in constants.items()})
 inputs=set(packet['inputs']);seen=set(inputs);references=set();operations={'add':0,'sub':0,'mul':0}
 for node in packet['nodes']:
  if node['id'] in seen:raise RuntimeError('duplicate node id')
  args=[]
  for x in node['args']:
   if isinstance(x,int):args.append([x%PRIME])
   elif x in seen:args.append(values[x]);references.add(x)
   else:raise RuntimeError('undefined node: '+x)
  op=node['op'];operations[op]+=1
  values[node['id']]=mul(*args) if op=='mul' else add(*args,minus=(op=='sub'))
  seen.add(node['id'])
 if set(packet['variables'])|set(packet['fixed_ports'])!=inputs:raise RuntimeError('input partition mismatch')
 if inputs-references:raise RuntimeError('dead mathematical input: '+str(inputs-references))
 if len(packet['nodes'])!=packet['live_binary_operations']:raise RuntimeError('operation mismatch')
 # Demand every arithmetic node is reachable, not merely a used prefix.
 byid={x['id']:x for x in packet['nodes']};reachable=set()
 def walk(x):
  if not isinstance(x,str) or x not in byid or x in reachable:return
  reachable.add(x)
  for a in byid[x]['args']:walk(a)
 walk(packet['output'])
 if reachable!=set(byid):raise RuntimeError('dead arithmetic nodes')
 f=values[packet['output']];norm=values[packet['norm_output']]
 if len(f)-1!=packet['exact_degree']:raise RuntimeError((packet['name'],'degree',len(f)-1,packet['exact_degree']))
 if f[-1]==0:raise RuntimeError('vanishing leading coefficient')
 return {'name':packet['name'],'variable_count':len(packet['variables']),'degree':len(f)-1,'norm_degree':len(norm)-1,'degree_lower_bound_certificate':{'prime':PRIME,'slopes':slopes,'coefficient':f[-1]},'binary_operations':operations,'live_binary_operations':len(packet['nodes'])}

def main():
 here=Path(__file__).resolve().parent
 root=Path(sys.argv[1]) if len(sys.argv)>1 else (here if (here/'coefficients/BINDING.json').exists() else here/'final_forms')
 constants=load_constants(root);results=[];start=time.time()
 for p in sorted(root.glob('integer*.json')):
  packet=json.loads(p.read_text())
  result=evaluate_univariate(packet,constants);result['file']=p.name;results.append(result)
  print(result['name'],result['degree'],result['norm_degree'],result['live_binary_operations'],'PASS',flush=True)
 receipt={'status':'PASS','scope':'Exact finite literal checks; upper bounds are proved by DEGREE_PROOF.md, finite specialization certifies matching nonzero leading terms. Not a consistency test or compiler formalization.','constants_mod_prime':{k:v%PRIME for k,v in constants.items()},'results':results,'elapsed_seconds':round(time.time()-start,3)}
 (root/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('All checked in',receipt['elapsed_seconds'],'seconds')
if __name__=='__main__':main()
