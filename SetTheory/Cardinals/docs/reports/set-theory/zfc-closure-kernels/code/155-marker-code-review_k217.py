#!/usr/bin/env python3
"""Independent local source/fold/relabel audit, no inherited compiler imports."""
from pathlib import Path
import argparse,hashlib,json,sys
if not __debug__ or sys.flags.optimize:
 raise SystemExit('Refusing optimized Python: run without -O/-OO and unset PYTHONOPTIMIZE; this audit requires assertions.')
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('package',type=Path,help='Final package with machine/* and evidence/runtime/*; the older flat frozen directory with runtime/* is also accepted')
ap.add_argument('--output',type=Path,help='Optional JSON receipt path')
args=ap.parse_args();P=args.package
M=P/'machine' if (P/'machine').is_dir()else P
R=P/'evidence/runtime' if M!=P else P/'runtime'
H=lambda b:hashlib.sha256(b).hexdigest()
for name,digest in {
 'baseline218.native.tm':'9c8505bf3731212192b83ee61dbc569085b4675ae9e0539843ae57d43ad9e886',
 'baseline_sites218.json':'264fba90229974a53c2c5c943cf5fe8924327b6bbc31bd47e64d7f5c670b7495',
 'prefold218.native.tm':'34617022def75d88a4f357589d7a48f468d17b58c910947ed0738aa3c6a5760a',
 'k217.native.tm':'c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099',
 'k217.tm':'a2b8bc2d4822962ad32819fe475a7d62b0d483bc4f41977bff292742f70b3e8c',
 'sites217.json':'9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655'
}.items():assert H((M/name).read_bytes())==digest,('file identity',name)
def get_table(name):
 d={}
 for line in (M/name).read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,r,w,dr,z=line.split();q,r,w,z=map(int,(q,r,w,z));assert r in(0,1)and w in(0,1)and dr in('L','R')
  assert(q,r)not in d;d[q,r]=(w,1 if dr=='R'else-1,z)
 return d
old=get_table('baseline218.native.tm');pre=get_table('prefold218.native.tm');new=get_table('k217.native.tm');can=get_table('k217.tm')
assert len(old)==len(pre)==436 and len(new)==len(can)==434
assert {k:(old[k],pre[k])for k in old if old[k]!=pre[k]}=={
 (201,0):((0,1,92),(0,1,188)),(188,0):((0,1,90),(0,1,92)),
 (188,1):((1,1,146),(1,1,90)),(210,0):((0,1,188),(0,1,146))}
for target,expected in[(69,[((53,1),(1,1,69))]),(400,[((224,0),(0,1,400))])]:
 assert[(k,v)for k,v in pre.items()if v[2]==target]==expected
assert pre[69,1]==pre[400,1]==(1,1,31)
assert pre[69,0]==(0,1,105)and pre[400,0]==(0,1,104)
expect={(q,r):(w,dr,69 if z==400 else z)for(q,r),(w,dr,z)in pre.items()if q!=400}
expect[69,0]=(0,-1,188);assert new==expect
for marker,target in[(0,104),(1,105)]:
 tape={-1:marker,0:0};q,x=69,0
 for _ in range(3):
  assert x in tape;w,dr,z=new[q,tape[x]];tape[x]=w;q=z;x+=dr
 assert(q,x)==(target,1)and tape=={-1:marker,0:0}
mp={int(k):v for k,v in json.loads((M/'canonicalization.json').read_text())['mapping'].items()}
assert len(mp)==218 and mp[0]==0 and mp[254]==217 and set(mp.values())==set(range(218))
assert{(mp[q],r):(w,dr,mp[z])for(q,r),(w,dr,z)in new.items()}==can
assert set(q for q,r in can)==set(range(217))
assert all((q,r)in can for q in range(217)for r in(0,1))
assert all(z in range(218)for w,dr,z in can.values())

def read_source(name):
 rs=json.loads((M/name).read_text());dd={r[0]:tuple(r[1:])for r in rs};assert len(dd)==len(rs)
 def build(path=''):
  if path in dd:return dd[path]
  assert any(p.startswith(path)for p in dd)
  return build(path+'0'),build(path+'1')
 t=build();out=[]
 def list_sites(v,p=''):
  if isinstance(v[0],str):out.append([p,*v])
  else:list_sites(v[0],p+'0');list_sites(v[1],p+'1')
 list_sites(t);assert out==rs
 return t,rs

def cfg(t,n):
 a=[]
 def size(v):return 1 if isinstance(v[0],str)else size(v[0])+size(v[1])
 def go(v,i,breaks,continues):
  if isinstance(v[0],str):
   op,r=v;assert i==len(a)
   dst=(i+1)%n
   if op=='CI':targets=(dst,)
   elif op=='CD':targets=((breaks[0]if breaks else 0),dst)
   elif op=='CB':targets=(breaks[r-1]if len(breaks)>=r else 0,)
   elif op=='CC':targets=(continues[r-1]if len(continues)>=r else 0,)
   else:assert op=='CH';targets=()
   a.append((op,r if op in('CI','CD')else None,targets));return
  lo,hi=v;mid=i+size(lo);end=(mid+size(hi))%n
  go(lo,i,[end]+breaks,continues);go(hi,mid,breaks,[i]+continues)
 go(t,0,[],[]);assert len(a)==n;return a

def bound(v):
 if isinstance(v[0],str):
  op,r=v;return (1,0,False)if op=='CD'else(r,0,False)if op=='CB'else(0,r,False)if op=='CC'else(0,0,op=='CH')
 a,b=map(bound,v);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2]
a,ar=read_source('baseline_sites218.json');b,br=read_source('sites217.json')
assert len(ar)==len(br)==4751 and[x[1:]for x in ar]==[x[1:]for x in br]
assert cfg(a,len(ar))==cfg(b,len(br))
p='11101001001110010'
def at(t):
 for x in p:t=t[int(x)]
 return t
a1=at(a);A=a1[0];B,C=a1[1][0][0];D=a1[1][0][1];E=a1[1][1]
assert all(bound(x)==(0,0,False)for x in[A,B,C,D,E])
assert at(b)==((A,B),((C,D),E))
for name,rs in [('before',ar),('after',br)]:
 outside={p:tuple([op,r])for p,op,r in rs if not p.startswith('11101001001')}
 if name=='before':save=outside
 else:assert save==outside
runtime=json.loads((R/'runtime.json').read_text());assert runtime['status']=='UNIVERSAL_MATHEMATICAL_PASS'and runtime['proved_cases']==runtime['expected_cases']==6176 and runtime['failures']==[]
assert runtime['table_sha256']==H((M/'k217.native.tm').read_bytes())
assert runtime['sites_sha256']==H((M/'sites217.json').read_bytes())
cases=json.loads((R/'runtime_cases.json').read_text())
expected_cases=[(i,positive)for i,(_,op,r)in enumerate(br)for positive in((False,True)if op=='CD'else(False,))]
assert expected_cases==[(r['site_index'],r['positive'])for r in cases]
assert all(r['duration'][0]>0 and all(n>=0 for n in r['duration'])for r in cases)
boot=json.loads((R/'startup.json').read_text())
q,x,ones=0,0,set()
for tick in range(boot['steps']):
 bit=int(x in ones);w,dr,z=new[q,bit]
 assert boot['trace'][tick]==[q,x,bit,w,dr,z]
 if w:ones.add(x)
 else:ones.discard(x)
 q=z;x+=dr
assert(q,x)==(84,-5)and ones==set(boot['one_cells'])
assert boot['registers']==[3,0,0,0,3,0,0,0,0]and boot['gap']==80 and boot['spares']==[1]*130
physical=[None]*9
for logical,physical_slot in enumerate((6,2,0,4,3,7,8,5,1)):physical[physical_slot]=boot['registers'][logical]
header=x+64+boot['gap'];expected_ones={x-1,header};cursor=header+1
for value in physical+boot['spares']:
 cursor+=1
 expected_ones.update(range(cursor,cursor+value+1));cursor+=value+1
assert ones==expected_ones and len(ones)==277
out=dict(status='INDEPENDENT_LOCAL_SOURCE_FOLD_RELABEL_PASS',source_cfg='equal by structured break/continue continuation stacks',source_primitives=4751,guard_cases=6176,protected_nonAX_primitives=len(save),component_boundaries=[bound(x)for x in[A,B,C,D,E]],working_states=217,transitions=434,fold_scope='arbitrary tape from start 0; two cells inspected; three steps replace one on read 0',runtime_receipt_identity_verified=True,blank_steps=boot['steps'],blank_complete_frame=True,one_cells=len(ones),spare_count=len(boot['spares']),native_sha256=H((M/'k217.native.tm').read_bytes()),canonical_sha256=H((M/'k217.tm').read_bytes()),source_sha256=H((M/'sites217.json').read_bytes()))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
