"""Audit serialized source/kernel identity and actual whole-tuple coefficients."""
import json,pathlib,collections,gzip,hashlib,copy
R=pathlib.Path(__file__).resolve().parent

def audit(s,k,c):
 n=len(s['variables']);w=c['weights'];q=c['targets_by_row'];out=[collections.defaultdict(int) for _ in q];indices={v:j for j,v in enumerate(q)}
 if len(indices)!=22 or len(set(w))!=31 or min(w)<1:raise ValueError('distinctness')
 cand=[[((),0,1)],[( (i,),w[i],1)for i in range(n)],[( (i,j),w[i]+w[j],1 if i==j else 2)for i in range(n)for j in range(i,n)]]
 for d,layer in enumerate(k['kernels']):
  seen=set()
  for t in layer['terms']:
   e=t['exponent']
   if e in seen or e<0:raise ValueError('exponent')
   seen.add(e)
   for inds,h,m in cand[d]:
    if e+h not in indices:continue
    a=[0]*n
    for i in inds:a[i]+=1
    for v in t['coefficient']:out[indices[e+h]][tuple(a)+tuple(v['powers'])]+=m*v['coefficient']
 for row,x in zip(s['equations'],out):
  if {tuple(t['powers']):2*t['coefficient']for t in row['terms']}!={a:v for a,v in x.items()if v}:raise ValueError('target mismatch')
 return True

def main():
 names=['gapN86','gapNq85','gapL86','gap87','split89'];results=[]
 for name in names:
  s=json.loads((R/(name+'_source.json')).read_text());k=json.loads((R/(name+'_kernels.json')).read_text());c=json.loads((R/(name+'_code.json')).read_text())
  audit(s,k,c);bad=copy.deepcopy(k);bad['kernels'][0]['terms'][0]['coefficient'][0]['coefficient']+=1
  try:audit(s,bad,c)
  except ValueError:pass
  else:raise ValueError('tamper accepted')
  results.append({'name':name,'identities':22,'coefficient_tamper_rejected':True})
 binding=json.loads((R/'coefficients/coefficients_binding.json').read_text());ports=[]
 for meta in binding['files']:
  p=R/'coefficients'/(meta['name']+'.bin.gz');z=p.read_bytes();raw=gzip.decompress(z)
  if hashlib.sha256(z).hexdigest()!=meta['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=meta['sha256']:raise ValueError('coefficient hash')
  v=int.from_bytes(raw,'little')
  if v.bit_length()!=meta['bit_length']:raise ValueError('coefficient size')
  ports.append(v)
 M=1<<2134927;maxbits=0
 for name in names:
  k=json.loads((R/(name+'_kernels.json')).read_text())
  for layer in k['kernels']:
   for t in layer['terms']:
    v=0
    for z in t['coefficient']:
     term=z['coefficient']
     for p,e in zip(ports,z['powers']):term*=p**e
     v+=term
    if abs(v)>=M:raise ValueError('bound')
    maxbits=max(maxbits,abs(v).bit_length())
 result={'status':'PASS','checks':results,'actual_port_bits':[v.bit_length()for v in ports],'kernel_coefficient_bits_max':maxbits,'coefficient_bound_exponent':2134927}
 (R/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
