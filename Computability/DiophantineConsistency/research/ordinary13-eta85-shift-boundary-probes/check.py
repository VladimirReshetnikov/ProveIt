from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-shift-boundary-probes')
parent=Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')
assert sha256(parent.read_bytes()).hexdigest()=='97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648'
# The generator is not run here because a read-only check must not rewrite probes.
g=json.loads(parent.read_text());assert len(g['source'])==85
w=[1,0,0,1,0,0,0,0,0,0,0,1,0];ports=[-1,0,1,0]
def ev(g,v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p))
 for n,op,a,b in g['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
def tree(g,shift=None):
 d={n:('v',i) for i,n in enumerate(g['witnesses'])};d.update({n:('p',i) for i,n in enumerate(g['fixed_numerals'])})
 if shift is not None:d[g['witnesses'][shift]]=('+',d[g['witnesses'][shift]],1)
 for n,op,a,b in g['source']:
  assert n not in d
  d[n]=(op,d[a] if isinstance(a,str) else a,d[b] if isinstance(b,str) else b)
 return d[g['output']]
results={}
for name,index in (('F',1),('alpha',2)):
 h=json.loads((D/(name+'-probe.json')).read_text());assert len(h['source'])==84
 assert h['witnesses']==g['witnesses'] and h['fixed_numerals']==g['fixed_numerals']
 assert tree(h,index)==tree(g)
 d=ev(h,w,ports);old=ev(g,w,ports)
 assert [d[n] for n in ('A0','A1','g72','Fa','out')]==[0,0,0,1,0]
 assert old['out']==9
 results[name]={'rows':84,'witness':w,'ports':ports,'parent_same_witness_output':old['out'],'probe_output':d['out']}
# Compact-like F=0, C=0 branch: the actual rank cannot be divisible by q^4
# under the positive low-mask and upper-bound assumptions. Finite controls
# supplement, but do not replace, the algebra in the README.
controls=0
for beta in range(2,13):
 for J in range(1,5):
  q=1+beta*J
  for MC in range(1,beta):
   for MF in range(2*beta):
    R=q*q*(q*q-1)+J*(MC+q*MF)
    assert math.gcd(J,q)==1 and 0<MC<q and R%(q**4)!=0
    controls+=1
print(json.dumps({'F_zero_C_zero_rank_controls':controls,
 'exact_parent_to_child_shift_identity_as_ordered_tree':True,
 'signed_port_full_zero_controls':results,'compact_port_or_reverse_zero_existence_proved':False,
 'lean_executed':False},sort_keys=True,indent=2))
