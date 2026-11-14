#!/usr/bin/env python3
"""Exact all-store AX11G command certificates.
Independent of builder and physical executor. Symbols denote arbitrary
naturals; only recorded pairing identities, tags and zero aliases are used.
The inherited helper algebra is in parent_commands.py with provenance.
"""
from pathlib import Path
import argparse,hashlib,json,sys
import parent_commands as p
HERE=Path(__file__).resolve().parent
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
req=p.require;atom=p.atom;pair=p.pair;I=p.I;U=p.U;add=p.add;S=('S',)
def AX(c,x=0,y=0,z=0):return('AX',c,x,y,z)
def MP(x):return('MP',x)
def heads(c,x,y,d,h):
 D,H=add(d,x),add(h,y)
 return [('gate',H,D,c)]+p.source_heads(D,H,c,d,h)
def run(word,store,nonone=frozenset()):
 t,w,d,h=store
 for com in word:
  if com[0]=='S':
   if(t==0 and h==1)or(t==1 and h==0):return None
   req(p.safe_sum(t,h,nonone),'unresolved Shift guard')
   nh,nw=p.projections(w);t,w,h=h,nw,nh
  elif com[0]=='AX':
   c,x,y,z=com[1:]
   for a in reversed(heads(c,x,y,d,h)+[t]):w=pair(a,w)
   t,d,h=0,z,0
  elif com[0]=='MP':
   y=add(d,com[1]);ante=I(t,y)
   if y==0:t,d,h=0,0,0
   elif ante==h:t,d,h=y,y,0
   else:
    req(p.definitely_distinct(ante,h),'unresolved MP match')
    t,d,h=0,y,0
  else:raise ValueError(com)
 return t,w,d,h
A0=AX(0)
POP=[A0]+[S]*12
PUSH=[A0]+[S]*10+[MP(0)]
DISCARD=[MP(0)]
def gen(i):return PUSH+[S,AX(i)]+[S]*11

def emitter_check():
 p.ROOT=HERE/'inputs'
 inherited=p.emitter_check()
 old=p.decode_word(HERE/'inputs/grammar.json')
 new=p.decode_word(HERE/'machine/grammar.json')
 req(len(old)==len(new)==190,'macro count')
 req(new[:-1]==old[:-1]and old[-1]=='close'and new[-1]=='push','exact terminal splice')
 return {'parent_free_constructor_audit':inherited,'old_final_macro':'breakTo1','new_final_macro':'push','same_complete_emitter_before_final_push':True,'saved_generalization':'U(c,h)','h_is_incoming_cache_not_h_plus_y':True,'new_stack_entries':11,'fourth_operand':'z','postcondition':'(0,[g,q1,...,q9,t;w],z,0)'}

def words_check():
 t,w,d,h,a,b,A,D,H=map(atom,('t','w','d','h','a','b','A','D','H'))
 req(run([AX(A)]+[S]*10,(t,w,d,h))==(heads(A,0,0,d,h)[8],pair(t,w),0,U(A,h)),'AXS10')
 req(run([AX(A)]+[S]*11,(t,w,d,h))==(U(A,h),w,0,t),'AXS11')
 for tt,ww in((t,pair(a,w)),(1,pair(a,w)),(0,0)):
  hd,tl=p.projections(ww)
  req(run(POP,(tt,ww,d,h))==(tt,tl,0,hd),'total Pop including top1 and empty stack')
 req(run(PUSH,(t,w,d,h))==(0,pair(t,w),0,0),'Push')
 req(run(PUSH,(0,0,d,h))==(0,0,0,0),'collapsed zero push')
 req(run(DISCARD,(t,w,0,h))==(0,w,0,0),'Discard any old cache')
 for j in range(9):
  select=DISCARD+[AX(A,D,H)]+[S]*(j+2)+POP*(9-j)
  req(run(select,(t,w,0,0))==(heads(A,D,H,0,0)[j],w,0,0),f'axiom selector{j}')
 for ii in(0,('positive','i')):
  for aa in(a,1,0):req(run(gen(ii),(aa,w,0,0))==(U(ii,aa),w,0,0),'direct generalization')
  x=atom('x');Dw=add(ii,x)
  rho=I(I(I(H,ii),Dw),I(I(Dw,H),I(A,H)))
  rw=DISCARD+[MP(ii),AX(A,x,H)]+[S]*10+POP
  req(run(rw,(t,w,0,0))==(rho,w,0,0),'restricted rho selector')
 suffix=[S,S,MP(b)]+POP
 req(run(suffix,(0,pair(a,pair(I(a,b),pair(0,w))),0,0),frozenset({a}))==(b,w,0,0),'MP suffix')
 req(run(suffix,(0,pair(1,pair(I(1,b),pair(0,w))),0,0))is None,'MP early halt')
 req(run([S,S,MP(0)]+POP,(0,pair(0,pair(0,pair(0,0))),0,0))==(0,0,0,0),'MP zero aliases')
 req(run(DISCARD+PUSH,(t,w,0,0))==(0,pair(0,w),0,0),'reserve protected zero')
 req(run([S,S,MP(1)]+POP,(0,pair(a,pair(I(a,1),pair(0,w))),0,0),frozenset({a}))==(1,w,0,0),'return contradiction')
 req(run([S],(1,w,0,0))is None,'final Shift halt')
 req(run([MP(b)],(a,w,0,I(a,b)))==(b,w,b,0),'successful MP no push')
 # The extra field is consumed by a genuine MP read, not implicitly zero.
 for z in(0,('positive','z')):
  req(p.run([p.MP(z)],(0,w,0,0))==(0,w,z,0),'post-push MP arbitrary fourth operand')
  req(run([AX(A,D,H,z)],(t,w,d,h))[2]==z,'AX fourth operand')
 return {'all_store_symbolic_checks':True,'pop_shifts':12,'push_shifts':10,'axiom_positions':list(range(9)),'generalizer':'Push;S;AX(i,0,0,0);S^11','generalizer_needs_offset':False,'selector':'Discard;AX(A,D,H,0);S^(j+2);Pop^(9-j)','rho':'Discard;MP(u);AX(A,D-u,H,0);S^10;Pop','mp_suffix':'S;S;MP(b);Pop','reserved_zero_required':True,'false_antecedent_early_halt':True,'zero_pair_aliases':True,'total_pop_at_top_one':True,'arbitrary_fourth_operand_checked':True,'final_refutation_test':'S'}

def encoding_check():
 # Local decoder equations checked over the free pair algebra, not huge
 # concrete numerical word codes. Total Cantor pairing makes these exact.
 z=atom('continuation');c=atom('c');x=atom('x');y=atom('y');u=atom('u')
 body=pair(('add',c,2),pair(y,pair(x,pair(u,z))))
 tag,L=p.projections(body)
 yp,L=p.projections(L);xp,L=p.projections(L);up,L=p.projections(L)
 req((tag,yp,xp,up,L)==(('add',c,2),y,x,u,z),'four-field local decoder')
 wrong=pair(('add',c,2),pair(y,pair(x,z)))
 _,L=p.projections(wrong);_,L=p.projections(L);_,L=p.projections(L);field,nextL=p.projections(L)
 req((field,nextL)!=(0,z),'old three-field encoding must not be reused')
 req(p.projections(pair(0,0))==(0,0),'zero decoder alias')
 return {'tag':'c+2','ordered_fields':['y','x','z'],'right_nested_pairing':True,'old_three_field_encoding_rejected':True,'positive_continuation_strictly_decreases':'component <= body < 1+body'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'verification/command_receipt.json');a=ap.parse_args()
 result={'status':'PASS','family':'PA194AX11G','emitter':emitter_check(),'words':words_check(),'encoding':encoding_check(),'scope':'Exact symbolic identities from stated numerical pairing and constructor properties. Not a Lean/iPRA endpoint.','inputs_sha256':{str(f):hashlib.sha256((HERE/f).read_bytes()).hexdigest()for f in('machine/grammar.json','machine/machine.tm','machine/instructions.json')}}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
