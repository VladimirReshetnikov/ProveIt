#!/usr/bin/env python3
"""Exact balanced Euclidean factorization from pinned inert matrix JSON."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

PINS={
 'matrix193_synchronized_rows.json':'9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233',
 'matrix193_synchronized_rows.md':'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
 'matrix193_context_absorption.json':'73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
 'matrix193_gamma1_recode.json':'9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'matrix193_marked_loader_packing.py':'280b83f46c9a5fc5ff931db6a2051386b874596ca172995eb22938c206b42653',
 'matrix193_marked_loader_packing.json':'2d9e99f33e12049be2b2228e388072df6ae024115d7942d9dbc4afc4e6f93475',
 'matrix193_marked_loader_packing.md':'0a093975e246141a4b4938f76bba1f4a74fec3ce4355534b363d7f28d42e36ac',
 'u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}
I=[1,0,0,1]
def need(b,s):
 if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def pairs(items):
 d={}
 for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def bad_constant(x):raise ValueError('nonfinite JSON: '+x)
def loads(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=bad_constant)
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def mm(a,b):return [a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]]
def inv(a):need(a[0]*a[3]-a[1]*a[2]==1,'determinant');return [a[3],-a[1],-a[2],a[0]]
def top(a):
 need(type(a) is list and len(a)==4 and all(type(r) is list and len(r)==4 for r in a),'4x4 shape')
 need(all(type(v) is int for r in a for v in r),'matrix integer types')
 return [a[0][0],a[0][1],a[1][0],a[1][1]]
def row(v,a):return [v[0]*a[0]+v[1]*a[2],v[0]*a[1]+v[1]*a[3]]
def shear(axis,q):return [1,q,0,1] if axis=='U' else [1,0,q,1]
def nearest(a,b):
 need(b!=0,'zero divisor')
 if b<0:a,b=-a,-b
 q,r=divmod(a,b)
 return q+int(2*r>=b) # exact nearest integer, ties toward +infinity

def factor(matrix):
 inv(matrix);a,b,c,d=matrix;rle=[];reductions=[]
 def put(axis,q):
  if not q:return
  if rle and rle[-1][0]==axis:q+=rle.pop()[1]
  if q:rle.append([axis,q])
 while a and c:
  olda,oldc=a,c
  if abs(a)>=abs(c):
   q=nearest(a,c);need(q!=0 and 2*abs(a-q*c)<=abs(c),'balanced U quotient')
   a,b=a-q*c,b-q*d;put('U',q);reductions.append(['U',q])
  else:
   q=nearest(c,a);need(q!=0 and 2*abs(c-q*a)<=abs(a),'balanced L quotient')
   c,d=c-q*a,d-q*b;put('L',q);reductions.append(['L',q])
  need(abs(a)+abs(c)<abs(olda)+abs(oldc),'Euclidean descent')
  need(a*d-b*c==1,'reduction determinant')
 swapped=a==0
 if swapped:
  a,b,c,d=-c,-d,a,b
  for axis,q in [('U',1),('L',-1),('U',1)]:put(axis,q)
 need(c==0 and a in (-1,1) and d==a,'terminal triangular shape')
 sign=a
 if a==-1:
  for axis,q in [('U',1),('L',-1),('U',1)]*2:put(axis,q)
  put('U',-b)
 else:put('U',b)
 product=I[:]
 for axis,q in rle:product=mm(product,shear(axis,q))
 need(product==matrix,'exact run product')
 need(all(q!=0 for _,q in rle) and all(rle[i][0]!=rle[i-1][0] for i in range(1,len(rle))),'canonical runs')
 return {'matrix':matrix,'runs':rle,'run_count':len(rle),'unit_length':sum(abs(q) for _,q in rle),'euclidean_reductions':reductions,'terminal_swap':swapped,'terminal_sign':sign,'verified_run_product':product}

def physical_word(record,side):
 # Row-right multiplication U changes coordinate1; L changes coordinate0.
 word=[]
 for axis,q in record['runs']:
  positive=3 if axis=='U' else 1
  if side=='Y':positive+=4
  letter=positive if q>0 else positive+1
  word.extend([letter]*abs(q))
 return word

def physical_pair(word):
 a=I[:];b=I[:]
 for label in word:
  need(type(label) is int and 1<=label<=8,'physical label')
  m=a if label<=4 else b;l=(label-1)%4+1;s=1 if l%2 else -1
  if l<=2:m[0]+=s*m[1];m[2]+=s*m[3]
  else:m[1]+=s*m[0];m[3]+=s*m[2]
 return a,b

def reconstruct(generators,tile_ids):
 by={g['name']:top(g['matrix']) for g in generators};need(len(by)==193,'generator count')
 C=by['C'];Ci=inv(C);table=[]
 for i in tile_ids:
  H=by['A'+str(i)];G=inv(by['B'+str(i)]);K=mm(mm(Ci,H),C)
  table.append({'tile_id':i,'H':H,'K':K,'G':G})
 return C,table

def compile_table(name,C,table,loader,switch_kind):
 load=factor(loader);load_word=physical_word(load,'Y');need(physical_pair(load_word)==(I,loader),'expanded LOAD')
 macros=[{'macro_id':0,'name':'LOAD','hub':0,'tile_id':None,'K':I,'G':loader,'factorizations':{'G':load},'physical_word':load_word}]
 for i,r in enumerate(table,1):
  k=factor(r['K']);g=factor(r['G']);word=physical_word(k,'X')+physical_word(g,'Y')
  need(word and physical_pair(word)==(r['K'],r['G']),'expanded paired product')
  macros.append({'macro_id':i,'name':'TILE'+str(r['tile_id']),'hub':1,'tile_id':r['tile_id'],'K':r['K'],'G':r['G'],'factorizations':{'K':k,'G':g},'physical_word':word})
 edges=[];next_state=2
 for macro in macros:
  w=macro['physical_word'];hub=macro['hub'];interior=list(range(next_state,next_state+len(w)-1));next_state+=len(w)-1;vertices=[hub]+interior+[hub]
  first=len(edges)
  for j,l in enumerate(w):edges.append([len(edges),vertices[j],vertices[j+1],l,macro['macro_id']])
  macro['first_edge']=first;macro['edge_count']=len(w);macro['last_edge']=len(edges)-1
 switch_id=len(edges);edges.append([switch_id,0,1,0 if switch_kind=='identity' else 'R',None])
 idle_id=len(edges);edges.append([idle_id,1,1,0,None])
 n=len(edges);m=1
 while m<max(8,n,next_state):m*=2
 need(all(e[0]==i and 0<=e[1]<next_state and 0<=e[2]<next_state for i,e in enumerate(edges)),'edge indexing')
 incoming=Counter(e[2] for e in edges);outgoing=Counter(e[1] for e in edges)
 need(all(incoming[s]==outgoing[s]==1 for s in range(2,next_state)),'private internal states')
 need(sum(len(z['physical_word']) for z in macros)+2==n,'edge count')
 fs=[f for z in macros for f in z['factorizations'].values()];counts=Counter(l for z in macros for l in z['physical_word'])
 stat={'matrices_factored':len(fs),'paired_tile_macros':96,'LOAD_macros':1,'RLE_runs':sum(z['run_count'] for z in fs),'unit_shears':n-2,'LOAD_unit_length':len(load_word),'max_run_magnitude':max(abs(q) for z in fs for _,q in z['runs']),'max_individual_matrix_word':max(z['unit_length'] for z in fs),'max_paired_tile_word':max(len(z['physical_word']) for z in macros[1:]),'max_matrix_entry':max(abs(v) for z in fs for v in z['matrix']),'max_matrix_entry_bits':max(abs(v).bit_length() for z in fs for v in z['matrix']),'controller_edges':n,'controller_states':next_state,'max_state_code':next_state-1,'padded_m':m,'log2_m':m.bit_length()-1,'unit_label_populations':{str(l):counts[l] for l in range(1,9)},'identity_switch_packing_bound':9*n+3*(m.bit_length()-1)+210,'identity_switch_positive_witness_bound':n+29}
 return {'name':name,'C':C,'transition_table':table,'macros':macros,'controller':{'edge_schema':['edge_id','source','target','physical_label_or_R','macro_id_or_null'],'edges':edges,'initial_hub':0,'final_hub':1,'marked_LOAD_edge':0,'SWITCH_edge':switch_id,'IDLE_edge':idle_id,'switch_kind':switch_kind},'statistics':stat}

def trajectory(packet,tiles,initial,R=None):
 macro={m['tile_id']:m for m in packet['macros'][1:]};v=list(initial);labels=0;state=0;maxbits=max(abs(z).bit_length() for z in v);digest=hashlib.sha256()
 # The saved fixture has ordinary input zero: SWITCH occurs immediately.
 if R is not None:v[2:]=row(v[2:],R)
 state=1;digest.update(('|'.join(hex(z) for z in v)+'\n').encode())
 for tid in tiles:
  mmacro=macro[tid]
  for j,label in enumerate(mmacro['physical_word']):
   edge=packet['controller']['edges'][mmacro['first_edge']+j];need(edge[1]==state,'physical fixture controller');state=edge[2]
   offset=0 if label<=4 else 2;l=(label-1)%4+1;s=1 if l%2 else -1
   if l<=2:v[offset]+=s*v[offset+1]
   else:v[offset+1]+=s*v[offset]
   labels+=1;maxbits=max(maxbits,*(abs(z).bit_length() for z in v));digest.update(('|'.join(hex(z) for z in v)+'\n').encode())
 need(state==1 and v[:2]==v[2:],'accepted expanded trajectory')
 return {'ordinary_input':0,'tile_steps':len(tiles),'unit_steps':labels,'switch_steps':1,'initial_row_coordinates':list(initial),'final_row_coordinates_hex':[hex(z) for z in v],'max_coordinate_bits':maxbits,'full_physical_state_stream_sha256':digest.hexdigest(),'every_transition_verified':True,'endpoint_equal':True,'positive_input_acceptance_claimed':False}

def make(root):
 data={}
 for n,pin in PINS.items():
  raw=(root/n).read_bytes();need(sha(raw)==pin,'dependency pin '+n);data[n]=raw
 sync=loads(data['matrix193_synchronized_rows.json']);ctx=loads(data['matrix193_context_absorption.json']);original=loads(data['matrix193_gamma1_recode.json']);prior=loads(data['matrix193_marked_loader_packing.json'])
 need(prior['packet']['ledger']['gates']==187,'inherited diagnostic pin/schema')
 tids=[r['tile_id'] for r in sync['transition_table']];need(len(tids)==len(set(tids))==96,'tiles')
 C,table=reconstruct(ctx['packet']['generators'],tids);need(exact(table,sync['transition_table']),'context table reconstruction')
 C0,oldtable=reconstruct(original['packet']['generators'],tids)
 B=ctx['block']['B'];need(B==[-52109,29036,-94920,52891],'loader block');loader=inv(B)
 first=compile_table('saved_context_absorbed',C,table,loader,'identity')
 second=compile_table('original_fixed_table',C0,oldtable,loader,'single_fixed_matrix_R')
 need([first['statistics'][k] for k in ['RLE_runs','unit_shears','controller_edges','padded_m']]==[7176,32819,32821,65536],'context census')
 need([second['statistics'][k] for k in ['RLE_runs','unit_shears','controller_edges','padded_m']]==[4780,19611,19613,32768],'original census')
 L=ctx['packet']['L'];R=ctx['packet']['R'];need(len(L)==len(R)==4,'context matrices')
 Li=inv(L);Ri=inv(R);need(C==mm(mm(Li,C0),Ri),'central context identity')
 for new,old in zip(table,oldtable):
  need(new['K']==mm(mm(R,old['K']),Ri),'K conjugation')
  need(new['G']==mm(mm(R,old['G']),Ri),'G conjugation')
 init=C[:2]+[1,0];uin=mm(Li,C0)[:2]+[1,0]
 fixtures=[trajectory(first,sync['accepting_fixture']['tile_sequence'],init),trajectory(second,sync['accepting_fixture']['tile_sequence'],uin,R)]
 need(fixtures[0]['tile_steps']==83 and fixtures[1]['tile_steps']==83,'fixture tiles')
 for a,b in zip([int(z,16) for z in fixtures[1]['final_row_coordinates_hex']],row([int(z,16) for z in fixtures[0]['final_row_coordinates_hex'][:2]],R)*2):need(a==b,'fixture frame relation')
 first['packing_scope']={'complete_arithmetic_DAG_emitted':False,'inherited_general_construction_applies':True,'complete_operation_upper_bound':first['statistics']['identity_switch_packing_bound'],'positive_witness_upper_bound':first['statistics']['identity_switch_positive_witness_bound'],'Hfix':max(first['statistics']['padded_m'],1+max(abs(z) for z in init)),'numerical_universal_bound':False,'reason':'saved [110 / A0] context is not asserted universal; arbitrary context-absorbed tables have different shear lengths'}
 second['packing_scope']={'complete_arithmetic_DAG_emitted':False,'matrix_R_switch_paid_here':False,'identity_switch_comparator_bound':second['statistics']['identity_switch_packing_bound'],'universal_operation_upper_bound_claimed':False,'reason':'fixed original TILE/LOAD geometry is compiled; nonidentity R switch must be charged in a separate packing extension'}
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'scope':'Complete effective RLE and literal unit-shear/controller expansions for actual contextual and original fixed96 tables; no emitted history DAG or new universal bound','predecessor_code_executed':False,'algorithm':{'quotient':'nearest integer, ties toward positive infinity','choice':'reduce the larger absolute first-column entry','canonicalization':'merge adjacent equal-axis runs, delete exponent zero','U':'[[1,q],[0,1]]','L':'[[1,0],[q,1]]','physical_labels':{'1':'X0+=X1','2':'X0-=X1','3':'X1+=X0','4':'X1-=X0','5':'Y0+=Y1','6':'Y0-=Y1','7':'Y1+=Y0','8':'Y1-=Y0','0':'identity','R':'one fixed right action Y->Y*R, not a unit shear'}},'packets':[first,second],'fixture_context':{'U':ctx['packet']['U'],'V':ctx['packet']['V'],'L':L,'R':R,'original_initial_coordinates':uin},'accepting_physical_traces':fixtures,'checked_matrix_factorizations':386,'expanded_unit_steps_checked':first['statistics']['unit_shears']+second['statistics']['unit_shears'],'universal_bound_improved':False}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);a=ap.parse_args();r=make(a.root)
 if a.expect:need(exact(r,loads(a.expect.read_bytes())),'receipt mismatch')
 else:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','tables':[p['statistics'] for p in r['packets']],'receipt_factorizations':r['checked_matrix_factorizations']}))
if __name__=='__main__':main()
