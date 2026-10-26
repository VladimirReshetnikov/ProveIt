"""Independent exact square-frame reconstruction for the strict integer source.
No producer imports; portable check of the sharpened pooling hypotheses.
"""
from pathlib import Path
from collections import defaultdict
import json,hashlib,argparse

def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def mul(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
 return {m:c for m,c in d.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def check(path):
 raw=path.read_bytes();eq=json.loads(raw);ns={v['name']:i for i,v in enumerate(eq['variables'])}
 ps=[{tuple(m):c for c,m in r['terms']} for r in eq['residuals']]
 labels={r['label']:i for i,r in enumerate(eq['residuals'])}
 def V(s):return {(ns[s],):1}
 def C(n):return {():n} if n else {}
 t=V('t0');F=V('crt.growth_majorant_F');q=add(C(1),scale(4,V('radix.odd_square_root_half')))
 # The cap row identifies the affine nominal anchor index h.
 cap=ps[labels['cap.index_residue']]
 h=scale(-1,{m:c for m,c in cap.items() if len(m)==1 and m!=(ns['cap.R'],)})
 if add(cap,h,scale(-1,V('cap.R')),scale(4,mul(V('index15.Y'),V('cap.h')))):
  raise ValueError('anchor cap row differs')
 atoms=[('t',t),('x',V('x')),('y+1',V('y')),('F',F),('F+t',add(F,t)),('B',V('choose0.output')),
        ('a',add(V('crt.encoded.a'),C(-1)))]
 atoms += [(k,V('crt.encoded.'+k)) for k in ['b','c','d','S','Sp','u','vq']]
 atoms += [('C',V('crt.encoded_index_minus_one')),('N',V('pow1.output')),('h',h),('q',q),('q+1',add(q,C(1))),('BH',V('self_radix.BH'))]
 ids=[3,4,5,7,8,9,10,11,12,13,14,15,16,17]
 atoms += [('pow'+str(i)+'.output',V('pow'+str(i)+'.output')) for i in ids]
 target=add(V('shared.W'),C(-2),*(scale(-1,mul(a,a)) for _,a in atoms))
 expected_mul40=add(V('mul.40'),C(-1),scale(-1,mul(add(V('crt.encoded.a'),V('crt.encoded.b')),add(V('crt.encoded.a'),V('crt.encoded.b')))))
 hits=[i for i,p in enumerate(ps) if p==expected_mul40]
 if len(hits)!=1:raise ValueError('expected unique mul.40 graph')
 combo=([(1,labels['shared.frame_definition']),(1,hits[0])] if 'add.380' in ns else [(1,labels['shared.frame_definition']),(1,labels['domain_guard.3']),(2,hits[0])])
 actual=add(*(scale(c,ps[i]) for c,i in combo))
 if actual!=target:raise ValueError(('frame reconstruction fails',terms(add(actual,scale(-1,target)))))
 at=[a for _,a in atoms]
 req_indices={0:t,1:V('x'),2:V('x'),3:add(F,t),4:t,5:add(V('crt.encoded.a'),C(-1)),7:V('crt.encoded.b'),8:V('crt.encoded.c'),9:V('crt.encoded.d'),10:V('crt.encoded.S'),11:V('y'),12:V('crt.encoded.Sp'),13:V('crt.encoded.u'),14:V('x'),15:V('crt.encoded.vq'),16:V('crt.encoded_index_minus_one'),17:h}
 bases={0:t,1:V('choose0.output'),2:V('self_radix.BH')}
 bases.update({i:add(q,C(1)) for i in [3,5,7,8,9,10,12,13,15,16,17]});bases.update({i:q for i in [4,11,14]})
 outputs={0:F,1:V('pow1.output'),2:q};outputs.update({i:V('pow'+str(i)+'.output') for i in ids})
 for i,k in req_indices.items():
  for role,a in [('base',bases[i]),('index',k),('output',outputs[i])]:
   if a not in at:raise ValueError(('missing frame atom',i,role))
 return {'path':str(path),'equation_sha256':hashlib.sha256(raw).hexdigest(),'passed':True,'frame_identity':'W=2+sum(atom^2)','atom_count':len(atoms),'row_combination':combo,'requests_covered':sorted(req_indices),'actual_atoms':[{'label':k,'terms':terms(p)} for k,p in atoms]}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('source',type=Path);a.add_argument('--output',type=Path);q=a.parse_args();result=check(q.source);s=json.dumps(result,sort_keys=True,indent=2)+'\n';print(s)
 if q.output:q.output.write_text(s)
