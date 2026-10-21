"""Owned standalone certificate checker; Python standard library only.
Local templates cannot read opaque exterior cells. This is not a Lean/Rocq proof.
"""
from pathlib import Path
import json,hashlib
D=Path(__file__).parent

def table(p):
 T={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in T
  assert b in(0,1)and w in(0,1)and d in('L','R');T[q,b]=(w,1 if d=='R'else-1,z)
 return T

def verify(name):
 p=D/'inputs'/f'{name}.tm';s=D/'inputs'/f'{name}.sites.json';pin=json.load(open(D/'pins.json'))[name]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['table_sha256']
 assert hashlib.sha256(s.read_bytes()).hexdigest()==pin['source_sha256']
 T=table(p);sites=json.load(open(s));leaves={x[0]:tuple(x[1:])for x in sites};assert len(leaves)==len(sites)
 assert all(set(p)<=set('01') and 0<len(p)<=48 for p in leaves)
 nodes=[];ids={}
 def build(pre):
  n=('leaf',)+leaves[pre]if pre in leaves else('fork',build(pre+'0'),build(pre+'1'))
  if n not in ids:ids[n]=len(nodes);nodes.append(n)
  return ids[n]
 root=build('');product=json.load(open(D/f'{name}_DECODER_PRODUCT.json'));assert nodes==[tuple(x)for x in product['nodes']]
 assert product['root']==[root,84,'1']
 templates={}
 for m in json.load(open(D/f'{name}_DECODER_MACROS.json'))['templates']:
  word=m['window'];assert 1<=len(word)<=3 and set(word)<=set('01')
  bits=list(map(int,word));original=bits.copy();h=len(bits)-1;q=m['input_state'];trace=[]
  assert 0<m['steps']<=100
  for _ in range(m['steps']):
   assert 0<=h<len(bits),'Opaque exterior read rejected'
   b=bits[h];w,d,z=T[q,b];trace.append([q,h-(len(bits)-1),b,w,d,z]);bits[h]=w;h+=d;q=z
  assert trace==m['trace'] and h==len(bits)and bits==original and q==m['output_state']
  key=(m['input_state'],word);assert key not in templates;templates[key]=q
 edges={}
 for e in product['edges']:
  k=tuple(e['state'])+(e['bit'],);assert k not in edges;edges[k]=e['result']
 pending=[(root,84,'1')];visited=set();used=set();exposed=set()
 while pending:
  st=pending.pop()
  if st in visited:continue
  visited.add(st);node,q,ctx=st;assert 1<=len(ctx)<=2 and set(ctx)<=set('01')
  n=nodes[node];assert n[0]=='fork'
  for b in '01':
   k=st+(b,);assert k in edges;used.add(k);v=edges[k];child=n[1+int(b)];assert child<node;cn=nodes[child]
   if cn[0]=='leaf':
    assert v==['leaf',cn[1],cn[2],q,ctx,b];exposed.add(tuple(v));continue
   candidates=[templates[q,(ctx+b)[-w:]]for w in range(1,min(3,len(ctx+b))+1)if(q,(ctx+b)[-w:])in templates]
   assert candidates and len(set(candidates))==1
   nxt=(child,candidates[0],(ctx+b)[-2:]);assert v==['next',*nxt];pending.append(nxt)
 assert used==set(edges)
 return dict(name=name,status='FRAMED_DECODER_CERTIFICATE_PASS',templates=len(templates),product_states=len(visited),edges=len(used),exposed_leaf_contexts=len(exposed),max_lookbehind=max(len(w)-1 for q,w in templates),scope='Internal decoder only; no generic leaf-return theorem or kernel compilation claimed.')
if __name__=='__main__':
 for name in ('K215_Formal','K215','ST215','GC_ZC215'):print(json.dumps(verify(name)))
