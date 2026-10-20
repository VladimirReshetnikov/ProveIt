#!/usr/bin/env python3
"""Independent exact source/emitter and closed-Hilbert binding check.

Standard library only. No source generator, allocator, or search module is imported.
The baseline macro contracts are inherited from the hash-pinned certified K224
source. Full TM runtime/startup and conditional-K calibration are separate layers.
"""
import argparse,copy,hashlib,json
from functools import lru_cache
from pathlib import Path
from check_fusion_certificate import check as check_hilbert

BASE_SHA='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'
PART_PATH='11101001001110'
MACRO_PATHS={166:'11101001001000',121:'11101001001001',168:'111010010011001000',119:'11101001001010',180:'1110100100101',218:'1110100100111000111011',177:'111010010011100011100'}
def need(p,msg):
 if not p:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def leaf(n):return isinstance(n[0],str)
def read_tree(rows):
 d={p:(op,arg)for p,op,arg in rows};need(len(d)==len(rows),'duplicate source path')
 prefixes={p[:i]for p in d for i in range(len(p)+1)}
 def go(p):
  if p in d:
   need(p+'0'not in prefixes and p+'1'not in prefixes,'non-prefix-free source');return d[p]
  need(p+'0'in prefixes and p+'1'in prefixes,'incomplete source tree')
  return go(p+'0'),go(p+'1')
 return go('')
def at(n,p):
 for b in p:need(not leaf(n),'path crosses leaf');n=n[int(b)]
 return n
def replace(n,p,x):
 if not p:return x
 b=int(p[0]);z=list(n);z[b]=replace(n[b],p[1:],x);return tuple(z)
def rows(n,p=''):
 if leaf(n):return [(p,*n)]
 return rows(n[0],p+'0')+rows(n[1],p+'1')
@lru_cache(None)
def flat(n):return(n,)if leaf(n)else flat(n[0])+flat(n[1])
def cover(n,s,e):
 if s==0 and e==len(flat(n)):return[n]
 need(not leaf(n),'bad interval');k=len(flat(n[0]))
 if e<=k:return cover(n[0],s,e)
 if s>=k:return cover(n[1],s-k,e-k)
 return cover(n[0],s,k)+cover(n[1],0,e-k)
def seq(xs):
 need(bool(xs),'empty sequence');n=xs[0]
 for x in xs[1:]:n=n,x
 return n

def graph(n):
 rr=rows(n);index={p:i for i,(p,_,_)in enumerate(rr)}
 def first(p):
  while p not in index:p+='0'
  return index[p]
 def after(p):
  while p.endswith('1'):p=p[:-1]
  return first(p[:-1]+'1')if p else first('')
 def cut(p,bit,k):
  pos=[i for i,b in enumerate(p)if b==bit]
  return p[:pos[-k]]if len(pos)>=k else ''
 ans=[]
 for p,op,arg in rr:
  if op=='CI':targets=[after(p)]
  elif op=='CD':targets=[after(cut(p,'0',1)),after(p)]
  elif op=='CB':targets=[after(cut(p,'0',arg))]
  elif op=='CC':targets=[first(cut(p,'1',arg))]
  elif op=='CH':targets=[]
  else:raise ValueError('unknown instruction')
  ans.append([op,arg,targets])
 return ans

I=lambda a,b:('I',a,b);Q=lambda a,b:('Q',a,b);R=lambda a,b:('R',a,b);E=lambda a,b:('E',a,b)
N=lambda a:I(a,1);And=lambda a,b:N(I(a,N(b)));Ex=lambda x,a:N(Q(x,N(a)))
def expressions():
 a,b,c='a','b','c';m=c;r=R(b,c);S=Q(c,I(R(c,a),R(c,b)))
 Wo=Q(b,I(m,Ex(b,And(m,r))));Uo=Q(a,I(S,Wo));Ho=Q(b,I(r,Ex(a,And(m,Uo))))
 old_cond=I(m,Ex(c,And(r,Ho)))
 XA=lambda x,A,B:N(Q(x,I(A,N(B))))
 W=Q(b,I(m,XA(b,m,r)));U=Q(a,I(S,W));H=Q(b,I(r,XA(a,m,U)))
 K=I(m,XA(c,r,H));K_unconditional=XA(c,I(m,r),H)
 VR=I(R(a,b),Q(c,R(a,b)));VE=I(E(a,b),Q(R(a,b),E(a,b)))
 return And(old_cond,And(VR,VE)),N(I(K,I(VR,N(VE)))),N(I(K_unconditional,I(VR,N(VE)))),K,VR,VE

def word(t):
 if isinstance(t,str):return[{'a':166,'b':121,'c':168}[t]]
 if t==1:return[177]
 if t[0]=='I'and t[2]==1:return word(t[1])+[218]
 return word(t[1])+word(t[2])+[{'I':119,'Q':180,'R':181,'E':182}[t[0]]]

def bind_formula(cert,n):
 ts=cert['terms']
 def label(x):return'c'if x=='k'else R('a','b')if x=='kappa'else x
 def go(i):
  t=ts[i]
  if t[0]=='F':return 1
  if t[0]=='meta':need(t[1]=='m','wrong opaque matrix');return'c'
  if t[0]=='I':return I(go(t[1]),go(t[2]))
  if t[0]=='Q':return Q(label(t[1]),go(t[2]))
  if t[0]in('Rel','Eq'):return(R if t[0]=='Rel'else E)(label(t[1]),label(t[2]))
  raise ValueError('bad formula tag')
 return go(n)

def verify(base_bytes,candidate_bytes,cert_bytes):
 need(sha(base_bytes)==BASE_SHA,'wrong certified baseline source')
 base=read_tree(json.loads(base_bytes));candidate=read_tree(json.loads(candidate_bytes));cert=json.loads(cert_bytes)
 proof=check_hilbert(cert)
 need(cert.get('equality_binder')=='kappa'and cert.get('core')=='conditional','wrong certificate family')
 original,fused,baseline_bundle,core,vr,ve=expressions()
 need(bind_formula(cert,cert['old_bundle'])==original,'old conditional endpoint mismatch')
 need(bind_formula(cert,cert['fused_bundle'])==fused,'fused conditional endpoint mismatch')
 mac={i:at(base,p)for i,p in MACRO_PATHS.items()};mac[181]=(mac[119],('CI',1));mac[182]=(mac[180],('CI',1))
 need(mac[218]==(mac[177],mac[119]),'Neg is not PushOne then Imp')
 part=at(base,PART_PATH);pre=cover(part,0,1893);post=cover(part,3970,len(flat(part)))
 base_word=word(baseline_bundle);new_word=word(fused)
 need(flat(part)[1893:3970]==tuple(z for i in base_word for z in flat(mac[i])),'baseline interval does not emit original bundle')
 reference=replace(base,PART_PATH,seq(pre+[mac[i]for i in new_word]+post))
 need(replace(candidate,PART_PATH,('CI',8))==replace(base,PART_PATH,('CI',8)),'source differs outside declared block')
 need(flat(reference)==flat(candidate),'changed instruction word differs from exact conditional emitter')
 g=graph(candidate);need(g==graph(reference),'changed structured RM CFG differs from exact conditional emitter')
 # Negative control: an unchanged unconditional source must fail the word binding.
 need(flat(base)!=flat(reference),'conditional change was not actually made')
 return dict(status='PASS_EXACT_CONDITIONAL_SOURCE_AND_FUSION',baseline_source_sha256=sha(base_bytes),candidate_source_sha256=sha(candidate_bytes),certificate_sha256=sha(cert_bytes),macro_paths=MACRO_PATHS,part_path=PART_PATH,baseline_global_formula_interval=[2541,4618],local_formula_interval=[1893,3970],instruction_occurrences=len(g),cfg_sha256=sha(json.dumps(g,separators=(',',':')).encode()),outside_declared_block_unchanged=True,exact_cfg_equals_literal_emitter=True,gate='if c=a or c=b then 0 else canonical_expression',private_and_opaque_matrix='k=m=c',equality_helper='kappa=RelCode(a,b)=4*P(a,b)+1',canonical_word=new_word,original_expression=original,canonical_expression=fused,core_expression=core,VR=vr,VE=ve,hilbert=proof,scope='All natural register parameters, arbitrary opaque matrix code, all label coincidences, including codes0/1. Exact structured RM and closed-Hilbert binding only; full TM runtime/startup and mathematical equiconsistency are separate.')

def main():
 p=argparse.ArgumentParser();p.add_argument('--base-sites',type=Path,required=True);p.add_argument('--candidate-sites',type=Path,required=True);p.add_argument('--certificate',type=Path,default=Path(__file__).with_name('conditional_fusion_certificate.json'));p.add_argument('--output',type=Path,default=Path(__file__).with_name('source_emitter_binding.json'));a=p.parse_args()
 bb,cb,pb=a.base_sites.read_bytes(),a.candidate_sites.read_bytes(),a.certificate.read_bytes();result=verify(bb,cb,pb)
 bad=copy.deepcopy(json.loads(pb));bad['fused_bundle']=bad['old_bundle']
 try:verify(bb,cb,json.dumps(bad).encode())
 except ValueError:result['wrong_fusion_endpoint_rejected']=True
 else:raise ValueError('negative control accepted')
 try:verify(bb,bb,pb)
 except ValueError:result['unconditional_source_rejected']=True
 else:raise ValueError('unconditional source accepted')
 changed=json.loads(cb);changed[4618][2]=4
 try:verify(bb,json.dumps(changed).encode(),pb)
 except ValueError:result['changed_gate_rejected']=True
 else:raise ValueError('changed gate accepted')
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k in ['status','candidate_source_sha256','certificate_sha256','instruction_occurrences','cfg_sha256','hilbert','wrong_fusion_endpoint_rejected']},indent=2))
if __name__=='__main__':main()
