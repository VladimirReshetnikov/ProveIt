#!/usr/bin/env python3
"""Independent exact reviewer of two paid U21 joint recodings."""
import argparse,hashlib,json
from collections import Counter,deque
from pathlib import Path
AUTHOR_PINS={
'residue_affine_sparse_joint_recoding.py':'386f00228dd250a1c582a3bf93724e9732db71cdd8d4fea6828d0b78d06fe443',
'residue_affine_sparse_joint_recoding.json':'a3b00883d84e7c8e9a6aea04ec3e54776fe927f7193f60a04050246f32039284',
'residue_affine_sparse_joint_recoding.md':'16d4a9e60343eb4f8f4ee78e8d60e7aeb2ee73b8d045241dd4951e124cf7b404'}
PINS={
'residue_affine_sparse_recoded468.py':'4b73c18e91473205dfb50edaf3e289898af305b14781ca1e10ce8a2ec06d834f',
'residue_affine_sparse_recoded468.json':'1aa26a73ebce4e5a8cfeb443b7d2aa296bbf7816a5c842728f6a3862872936b4',
'residue_affine_sparse_recoded468.md':'93607b73b03769c46ec698c2b2d1bac83e3c192e81c9d29d4d000de66ef35ea7',
'residue_affine_sparse_recoded467.py':'08bea80dc49d502171f3786cf11c6e0b5b959c4812d8086543e4e66fc9ab4039',
'residue_affine_sparse_recoded467.json':'9b816825cfa560db664c2d262fd2a4815b2f28046f8d500675e6a38d5d48af70',
'residue_affine_sparse_recoded467.md':'adba76e7aa7d6155b0f568c9a83ecc6859536b65b150b63b60a06ffdf1d0acbd',
'residue_affine_sparse_factored.json':'39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda',
'residue_affine_sparse_program_radix504.md':'4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549',
'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
'residue_affine_sparse_terminal537.md':'9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1',
'residue_affine_sparse_scale538.md':'0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623'}
OLD_CODES=[0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14]
NEW_CODES=[0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14]
# Explicit alternative paid recipe; all affine values independently expanded below.
CONTROL=[
['joint_26','-','remainder_total_coefficient_group_160','edge_7'],
['joint_33','*',2,'joint_26'],['joint_44','+','edge_23','joint_33'],
['joint_45','+','joint_44','remainder_total_coefficient_163'],
['joint_34','*',6,'edge_29'],['joint_46','+','joint_45','joint_34'],
['joint_35','*',7,'prime_selector_112'],['joint_47','+','joint_46','joint_35'],
['joint_36','*',9,'edge_20'],['joint_48','+','joint_47','joint_36'],
['joint_27','+','edge_2','edge_10'],['joint_28','+','joint_27','edge_24'],
['joint_37','*',10,'joint_28'],['joint_49','+','joint_48','joint_37'],
['joint_38','*',13,'edge_31'],['joint_50','+','joint_49','joint_38'],
['joint_29','+','edge_13','prime_selector_102'],['joint_39','*',16,'joint_29'],
['joint_51','+','joint_50','joint_39'],['joint_52','+','joint_51','remainder_total_coefficient_167'],
['joint_40','*',20,'edge_3'],['joint_53','+','joint_52','joint_40'],
['joint_41','*',37,'control_codes__target_class_35'],['joint_54','+','joint_53','joint_41'],
['joint_30','+','edge_22','edge_26'],['joint_31','+','joint_30','edge_33'],
['joint_32','+','joint_31','edge_35'],['joint_42','*',39,'joint_32'],
['joint_55','+','joint_54','joint_42'],['joint_56','+','joint_55','selectors_70'],
['joint_43','*',4,'action_selector_126'],['joint_57','+','joint_56','joint_43'],
['joint_58','+','joint_57','prime_selector_111'],['joint_12','*',29,'control_codes__duplicate_state_2'],
['joint_59','+','joint_58','joint_12'],['joint_60','+','joint_59','control_codes__duplicate_state_8'],
['joint_61','-','joint_60','edge_0'],['joint_63','*','radix_86','joint_61'],
['joint_14','+','prime_selector_95','u21_grouped_J_0'],['joint_5','*',3,'prime_selector_97'],
['joint_15','+','joint_14','joint_5'],['joint_6','*',8,'prime_selector_101'],
['joint_16','+','joint_15','joint_6'],['joint_7','*',9,'prime_selector_109'],
['joint_17','+','joint_16','joint_7'],['joint_8','*',17,'prime_selector_113'],
['joint_18','+','joint_17','joint_8'],['joint_9','*',11,'prime_selector_115'],
['joint_19','+','joint_18','joint_9'],['joint_0','-','action_selector_123','selectors_36'],
['joint_10','*',4,'joint_0'],['joint_20','+','joint_19','joint_10'],
['joint_1','+','edge_14','control_codes__duplicate_state_8'],['joint_2','+','joint_1','edge_15'],
['joint_21','+','joint_20','joint_2'],['joint_11','*',21,'control_codes__duplicate_state_5'],
['joint_22','+','joint_21','joint_11'],['joint_23','+','joint_22','joint_12'],
['joint_3','+','control_codes__duplicate_state_3','control_codes__duplicate_state_6'],
['joint_13','*',32,'joint_3'],['joint_24','+','joint_23','joint_13'],
['joint_62','*',14,'scale_89'],['joint_64','+','joint_24','joint_62']]
OUT='norm_output';U='sparse_all_units';B='radix_86';P='scale_89'
def ck(v,s):
 if not v:raise ValueError(s)
def sha(v):return hashlib.sha256(v).hexdigest()
def enc(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def obj(xs):
  out={}
  for k,v in xs:ck(k not in out,'duplicate key');out[k]=v
  return out
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_float=bad,parse_constant=bad)
def table(rows):
 out={}
 for r in rows:
  ck(type(r)is list and len(r)==4,'row length');n,o,a,b=r
  ck(type(n)is str and n not in out and o in ['+','-','*'],'SSA/op')
  ck(all(type(x)in [int,str] for x in [a,b]),'operand type');out[n]=(o,a,b)
 return out
def closure(d,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n in d and n not in seen:seen.add(n);todo+=list(d[n][1:])
 return seen
def graph(rows,free):
 d=table(rows);known=set(free);deps={};users={n:[] for n in d}
 for n,o,a,b in rows:
  ck(n not in known and all(type(x)is int or x in known for x in [a,b]),'literal topological order')
  known.add(n);deps[n]={x for x in [a,b] if x in d}
  for x in deps[n]:users[x].append(n)
 queue=deque(n for n in d if not deps[n]);number=0
 while queue:
  n=queue.popleft();number+=1
  for u in users[n]:
   deps[u].remove(n)
   if not deps[u]:queue.append(u)
 ck(number==len(d),'independent Kahn check')
 ck(closure(d,[OUT])==set(d),'all rows live')
 used={x for r in rows for x in r[2:] if type(x)is str and x not in d}
 ck(used==set(free),'exact supplied ports live')
 c=Counter(r[1] for r in rows)
 return dict(total=len(rows),M=c['*'],A=c['+']+c['-'])
def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   z=tuple(sorted(m+n));out[z]=out.get(z,0)+c*d
 return {m:c for m,c in out.items() if c}
def expand(d,target,cuts):
 memo={n:{(n,):1} for n in cuts}
 def at(n):
  if type(n)is int:return {():n} if n else {}
  if n not in memo:
   ck(n in d,'uncut supplied value '+n);o,a,b=d[n];a,b=at(a),at(b)
   memo[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return memo[n]
 return at(target)
def serial(p):return [[list(k),v] for k,v in sorted(p.items())]
def affine(rows):
 z=(0,)*37;v={f'edge{i}_hat':tuple(int(j==i+1) for j in range(37)) for i in range(36)}
 for n,o,a,b in rows:
  aa=(a,)+z[1:] if type(a)is int else v.get(a)
  bb=(b,)+z[1:] if type(b)is int else v.get(b)
  if aa is None or bb is None:continue
  if o in ['+','-']:v[n]=tuple(x+(y if o=='+' else -y) for x,y in zip(aa,bb))
  elif not any(aa[1:]):v[n]=tuple(aa[0]*x for x in bb)
  elif not any(bb[1:]):v[n]=tuple(bb[0]*x for x in aa)
 return v

def degree(rows,free):
 raw={n:1 for n in free}
 for n,o,a,b in rows:
  x,y=[0 if type(v)is int else raw[v] for v in [a,b]];raw[n]=x+y if o=='*' else max(x,y)
 names=['native__wn2','native__R12','native__R10a','native__gam'];X,a,c,G=names
 actual=expand(table(rows),'native__R15',set(names))
 expect={tuple(sorted(m)):k for m,k in [([X,X],1),([a,c,X],2),([G,X],2),([a,c,G],2),([G,G],1),([a,c,c],-4),([c,c],-3)]}
 ck(actual==expect,'guarded seven-term main norm')
 weights={n:raw[n] for n in names};bound=max(sum(weights[n] for n in m) for m in actual)
 fresh={n:1 for n in free}
 for n,o,a,b in rows:
  x,y=[0 if type(v)is int else fresh[v] for v in [a,b]];fresh[n]=x+y if o=='*' else max(x,y)
  if n=='native__R15':fresh[n]=bound
 return dict(naive=raw[OUT],guarded=fresh[OUT],main=bound,weights=weights,control=fresh['norm_residual1'],
  unit=fresh[U],SOS=fresh['norm_sum5'],main_norm_coefficients=serial(actual))

def build(root,author_root):
 ck(len(AUTHOR_PINS)==3,'frozen author pins required')
 for base,pins in [(root,PINS),(author_root,AUTHOR_PINS)]:
  for n,h in pins.items():ck(sha((base/n).read_bytes())==h,'pin '+n)
 child=read(author_root/'residue_affine_sparse_joint_recoding.json');fact=read(root/'residue_affine_sparse_factored.json')
 ck(child['source_sha256']==AUTHOR_PINS['residue_affine_sparse_joint_recoding.py'],'author self binding')
 ck(len(child['packets'])==2,'exactly two emitted interfaces')
 table21=fact['default_table'];primes=fact['default_primes'];edges=[[0,0,'I',2,1,2,1,2],[0,1,'I',2,1,2,1,2]]
 for q,inst in enumerate(table21,1):
  op,reg,*targets=inst;prime=primes[reg];targets=[t+1 for t in targets]
  if op=='I':edges.append([q,targets[0],op,prime,1,prime,1,prime])
  else:
   ck(op in ['D','T'],'actual instruction opcode')
   edges.append([q,targets[0],op,prime,prime,1,prime,1] if op=='D' else [q,targets[0],op,prime,prime,prime,prime,prime])
   edges.append([q,targets[1],'Z',prime,prime,prime,1,1])
 ck(len(table21)==21 and len(edges)==36 and edges==fact['edges']==child['literal_edges'],'all actual edges')
 weights={2:0,3:1,5:2,7:3,11:8,13:9,17:17,19:11};correction={9:1,11:29,12:21,13:32,14:1,18:32}
 codes=[0]+[weights[primes[i[1]]]+4*(i[0]=='I')+correction.get(q,0) for q,i in enumerate(table21,1)]+[14]
 ck(codes==NEW_CODES==child['new_codes'] and OLD_CODES==child['old_codes'],'new actual state code recipe')
 ck(len(set(codes))==23 and max(codes)==40 and codes.count(0)==1 and len(set(OLD_CODES))==23 and max(OLD_CODES)==41,'bounded injective state codes')
 ck([(q,codes[q]-OLD_CODES[q]) for q in range(23) if codes[q]!=OLD_CODES[q]]==[(11,13),(12,-11),(18,16)],'only three state changes')
 results=[]
 for idx,stem in enumerate(['residue_affine_sparse_recoded468','residue_affine_sparse_recoded467']):
  parent=read(root/(stem+'.json'));snapshot=enc(parent);old=parent['packet'];case=child['packets'][idx];new=case['packet']
  ck(parent['source_sha256']==PINS[stem+'.py'],'parent binding');od,nd=table(old['source']),table(new['source'])
  ck(sha(enc(old['source']))==old['source_sha256'],'complete immediate-parent source binding')
  for k in ['parameters','witnesses','fixed_program_parameters','ordinary_input_parameter','output','literal_height_radix_rows','exact_degree_claimed','polynomial_degree_upper_bound']:
   ck(enc(old[k])==enc(new[k]),'retained interface '+k)
  recipes=['Fixed positive program E=3^e from the inherited U21 compiler; literal radix B=64*(E+x+height_slack), ordinary input x>0. Selected codes have maximum40, below B>=192.',
   'Fixed E=3^e; C is dyadic, C>=64 and C>E; B=C*(x+height_slack), ordinary input x>0. Selected codes have maximum40, below B>=128.']
  ck(new['valid_recipe']==recipes[idx],'updated recipe metadata states the actual maximum40')
  free=old['parameters']+old['witnesses'];ck(len(old['witnesses'])==67 and len(free)==69+idx,'interface size')
  base=closure(od,[U]+['norm_residual'+str(i) for i in [0,2,3,4,5]])
  ck(len(base)==389-idx,'independent retained pre-control base')
  finals={n:r for n,r in od.items() if n.startswith('norm_') and n not in base};ck(len(finals)==15,'actual tail15')
  expected={n:od[n] for n in base};expected.update(table(CONTROL));expected.update(finals)
  expected['norm_residual1']=('-','joint_63','joint_64')
  ck(expected==nd,'complete fresh expected source')
  ck(all(nd[n]==od[n] for n in base),'whole base literal')
  native=[n for n in od if n.startswith('native__')];ck(len(native)==72 and all(nd[n]==od[n] for n in native),'72 native definitions')
  nfinal=[n for n in od if n.startswith('norm_')];ck(len(nfinal)==20 and all(nd[n]==od[n] for n in nfinal if n!='norm_residual1'),'other19 full finalizer rows')
  heights=[['height_85','+','input','height_slack'],['radix_86','*','radix_program','height_85']] if idx else [['height_83','+','program','input'],['height_85','+','height_83','height_slack'],['radix_86','*',64,'height_85']]
  ck(old['literal_height_radix_rows']==heights and all(nd[r[0]]==tuple(r[1:]) for r in heights),'separate unchanged height recipes')
  go=graph(old['source'],free);gn=graph(new['source'],free)
  ck(gn==dict(total=467-idx,M=171,A=296-idx) and go==dict(total=468-idx,M=171,A=297-idx),'complete counted saving1A')
  ck(new['ledger']==dict(operations=467-idx,multiplications=171,additions_subtractions=296-idx,witnesses=67),'declared complete ledger')
  cert=[r for r in new['source'] if not r[0].startswith('norm_')];c=Counter(r[1] for r in cert)
  ck((len(cert),c['*'],c['+']+c['-'])==(447-idx,164,283-idx),'certificate rows')
  ck(new['certificate_ledger']==dict(operations=447-idx,multiplications=164,additions_subtractions=283-idx,equations=7,witnesses=67),'declared certificate ledger')
  av0,av1=affine(old['source']),affine(new['source']);ci0=old['control_interfaces'];ci1=new['control_interfaces']
  allword=[]
  for v,ci,cs in [(av0,ci0,OLD_CODES),(av1,ci1,NEW_CODES)]:
   for key,end in [('current',0),('following',1)]:
    vv=tuple(cs[e[end]] for e in edges);want=(-sum(vv),)+vv
    ck(v[ci[key]]==want,'full 36 hats with all constants')
    allword.append(dict(name=ci[key],affine_coefficients=list(want)))
  control_names=set(table(CONTROL));aff_names=control_names&set(av1)
  ck(len(aff_names)==60,'all60 affine control values')
  desired=(-3,)+tuple(int(i in [19,21,25]) for i in range(36))
  ck(av1['joint_26']==desired,'paid remainder prefix minus edge7')
  shared=closure(nd,[ci1['current']])&closure(nd,[ci1['following']])-base
  ck(shared=={'joint_12'} and nd['joint_12']==('*',29,'control_codes__duplicate_state_2'),'only shared29 product')
  unions=[]
  for d,ci in [(od,ci0),(nd,ci1)]:
   a=closure(d,[ci['current']])-base;b=closure(d,[ci['following']])-base;cc=Counter(d[n][0] for n in a|b)
   unions.append([len(a),len(b),len(a|b),cc['*'],cc['+']+cc['-']])
  ck(unions==[[23,38,61,20,41],[24,37,60,20,40]],'joint word costs')
  hats={f'edge{i}_hat' for i in range(36)};cuts=hats|{B,P,U}|{f'norm_residual{i}' for i in [0,2,3,4,5]}
  oldr=expand(od,'norm_residual1',cuts);newr=expand(nd,'norm_residual1',cuts);dr=add(newr,oldr,-1)
  dc=tuple(NEW_CODES[e[0]]-OLD_CODES[e[0]] for e in edges);dn=tuple(NEW_CODES[e[1]]-OLD_CODES[e[1]] for e in edges)
  def hatpoly(v):return {():-sum(v),**{(f'edge{i}_hat',):x for i,x in enumerate(v) if x}}
  delta=add(mul({(B,):1},hatpoly(dn)),hatpoly(dc),-1)
  ck(dr==delta,'literal complete control correction in actual hats')
  oldF=expand(od,OUT,cuts);newF=expand(nd,OUT,cuts)
  correction=mul({(U,):1},add(mul(newr,newr),mul(oldr,oldr),-1))
  ck(add(newF,oldF,-1)==correction,'full expanded actual-hat correction, not residual placeholders')
  formal=expand(nd,OUT,{U}|{f'norm_residual{i}' for i in range(6)})
  expectedF={():-1,(U,):1}
  for i in range(6):expectedF[tuple(sorted([U,f'norm_residual{i}',f'norm_residual{i}']))]=1
  ck(formal==expectedF,'actual full U*(1+SOS)-1')
  deg=degree(new['source'],free)
  ck((deg['guarded'],deg['naive'],deg['main'],deg['unit'],deg['SOS'],deg['control'])==[(5091,5157,816,4993,98,2),(5160,5227,827,5062,98,3)][idx],'independent complete degree bound')
  ck(enc(parent)==snapshot,'immutable parent object')
  ck(sha(enc(new['source']))==new['source_sha256'],'full emitted source hash')
  results.append(dict(interface=case['interface'],ledger=gn,base_rows=len(base),control_rows=63,finalizer_remaining_rows=15,
   native_rows=72,unchanged_finalizer_rows=19,old_new_word_costs=unions,shared_control=list(shared),
   actual_hat_words=allword,new_affine_intermediates={n:list(av1[n]) for n in sorted(aff_names)},
   actual_control_correction=serial(delta),full_output_correction=serial(correction),full_output_correction_terms=len(correction),
   literal_height_rows=heights,degree=deg))
 return dict(status='PASS_INDEPENDENT_U21_JOINT_RECODING',source_sha256=sha(Path(__file__).read_bytes()),
  author_pins=AUTHOR_PINS,parent_pins=PINS,actual_edges=edges,old_codes=OLD_CODES,new_codes=NEW_CODES,results=results,
  scope=dict(author_or_predecessor_execution=False,all36_hat_vectors=True,all933_new_rows_reconstructed=True,
   all_ring_full_correction=True,polynomials_identical_off_zero=False,same_positive_zeros='each source with its own parent on valid fixed recipe',
   cross_interface_positive_map=False,exact_degree_claim=False,new_native_histories=False))
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=Path);p.add_argument('--author-root',required=True,type=Path)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=p.parse_args();r=build(a.root,a.author_root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact typed reviewer receipt')
 print(r['status'],[x['ledger']['total'] for x in r['results']], 'actual-hat full corrections verified')
if __name__=='__main__':main()
