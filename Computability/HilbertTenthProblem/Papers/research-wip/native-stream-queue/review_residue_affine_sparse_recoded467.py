"""Independent actual470-to467 source/control proof; no predecessor execution."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path

AUTHOR={
'residue_affine_sparse_recoded467.py':'08bea80dc49d502171f3786cf11c6e0b5b959c4812d8086543e4e66fc9ab4039',
'residue_affine_sparse_recoded467.json':'9b816825cfa560db664c2d262fd2a4815b2f28046f8d500675e6a38d5d48af70',
'residue_affine_sparse_recoded467.md':'adba76e7aa7d6155b0f568c9a83ecc6859536b65b150b63b60a06ffdf1d0acbd'}
PINS={
'residue_affine_sparse_shared470.py':'6705f2abfc330427f47aaf8ee3cbad25ca311e86014e0499c994fdf90b97a586',
'residue_affine_sparse_shared470.json':'2f7715aa5449118cfad292595bc7cde374587723a123b3c69a0d180cb51993e4',
'residue_affine_sparse_shared470.md':'b50e62d1eedef24ef390562c70cca69bbbb4b2dd5d6c7f1134ed99b4fb278570',
'residue_affine_sparse_program_radix504.md':'4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549',
'residue_affine_sparse_factored.json':'39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda',
'residue_affine_sparse_factored.md':'b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7',
'residue_affine_sparse_control_codes.json':'2f9e97873bf4b02da0e6664bdf1ac150d4b3f5befb2bb5ae907c01c3c1dc7d9d',
'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
'residue_affine_sparse_terminal537.md':'9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1',
'residue_affine_sparse_scale538.md':'0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623'}
PROGRAM=[['D',1,1,2],['I',7,0],['I',6,3],['D',5,2,4],['D',6,5,3],['I',5,6],['D',7,7,8],['I',1,4],['T',6,9,0],['D',4,0,10],['D',5,11,12],['D',5,13,14],['D',2,17,18],['D',5,15,16],['D',3,17,19],['I',4,10],['I',2,20],['D',4,0,21],['D',0,0,17],['I',0,0],['I',3,17]]
PRIMES=[5,3,2,7,11,13,17,19]
OLDCODES=[0,1,14,21,9,17,13,10,5,18,8,25,41,32,57,3,12,4,24,2,6,7,63]
NEWCODES=[0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14]
# Independent explicit paid64-row recipe. Integers denote scalar literals;
# r-prefixed abbreviations here denote only newly paid recode registers.
SPEC=[
(0,'-','action_selector_123','selectors_36'),
(1,'+','control_codes__duplicate_state_8','edge_14'),(2,'+','r1','edge_15'),
(3,'+','control_codes__duplicate_state_3','control_codes__duplicate_state_2'),
(4,'+','control_codes__duplicate_state_6','control_codes__duplicate_state_5'),
(6,'*',3,'prime_selector_97'),(7,'*',8,'prime_selector_101'),
(8,'*',9,'prime_selector_109'),(9,'*',17,'prime_selector_113'),
(10,'*',11,'prime_selector_115'),(11,'*',4,'r0'),(12,'*',16,'r3'),(13,'*',32,'r4'),
(14,'+','u21_grouped_J_0','prime_selector_95'),(15,'+','r14','r6'),
(16,'+','r15','r7'),(17,'+','r16','r8'),(18,'+','r17','r9'),(19,'+','r18','r10'),
(20,'+','r19','r11'),(21,'+','r20','r2'),(22,'+','r21','r12'),(23,'+','r22','r13'),
(24,'+','edge_21','edge_25'),(25,'+','edge_18','edge_20'),
(26,'+','edge_2','edge_10'),(27,'+','r26','edge_24'),(28,'+','prime_selector_102','edge_13'),
(29,'+','edge_22','edge_26'),(30,'+','r29','edge_33'),(31,'+','r30','edge_35'),
(32,'*',2,'r24'),(33,'*',6,'edge_29'),(34,'*',7,'prime_selector_112'),
(35,'*',9,'r25'),(36,'*',10,'r27'),(37,'*',13,'edge_31'),(38,'*',16,'r28'),
(39,'*',20,'edge_3'),(40,'*',23,'r31'),(41,'*',24,'control_codes__target_class_35'),
(42,'*',4,'action_selector_126'),(43,'*',31,'control_codes__duplicate_state_2'),
(44,'+','edge_23','r32'),(45,'+','r44','remainder_total_coefficient_163'),
(46,'+','r45','r33'),(47,'+','r46','r34'),(48,'+','r47','r35'),(49,'+','r48','r36'),
(50,'+','r49','r37'),(51,'+','r50','r38'),(52,'+','r51','remainder_total_coefficient_167'),
(53,'+','r52','r39'),(54,'+','r53','r40'),(55,'+','r54','r41'),
(56,'+','r55','selectors_70'),(57,'+','r56','r42'),(58,'+','r57','prime_selector_111'),
(59,'+','r58','r43'),(60,'+','r59','control_codes__duplicate_state_8'),
(61,'-','r60','edge_0'),(62,'*','radix_86','r61'),(63,'*',14,'scale_89'),(64,'+','r23','r63')]
OUT='norm_output'
def ck(v,s):
 if not v:raise ValueError(s)
def sha(v):return hashlib.sha256(v).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def defs(rows):
 d={}
 for r in rows:
  ck(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  ck(type(n)is str and n not in d and o in ['+','-','*'],'SSA/op')
  ck(all(type(v)in [str,int] for v in [a,b]),'operand type');d[n]=r
 return d
def closure(d,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in d:todo.extend(d[n][2:])
 return seen
def ledger(rows):
 c=Counter(r[1] for r in rows);return dict(total=len(rows),M=c['*'],A=c['+']+c['-'])
def audit(rows,free):
 d=defs(rows);known=set(free)
 ck(len(known)==len(free),'distinct free')
 for n,o,a,b in rows:
  ck(n not in known and all(type(v)is int or v in known for v in [a,b]),'topology');known.add(n)
 ck(closure(d,[OUT])==known,'all rows and ports live');return ledger(rows)
def add(a,b,s=1):
 d=dict(a)
 for m,c in b.items():d[m]=d.get(m,0)+s*c
 return {m:c for m,c in d.items() if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
 return {m:c for m,c in d.items() if c}
def poly(rows,root,cuts):
 d=defs(rows);e={n:{(n,):1} for n in cuts}
 def at(n):
  if type(n)is int:return {():n} if n else {}
  if n not in e:
   ck(n in d,'missing polynomial boundary '+n);_,o,a,b=d[n];x,y=at(a),at(b)
   e[n]=mul(x,y) if o=='*' else add(x,y,1 if o=='+' else -1)
  return e[n]
 return at(root)
def plist(p):return [[list(m),c] for m,c in sorted(p.items())]
def build_edges():
 # Independently expand each U21 row into its positive/zero branches.
 e=[[0,0,'I',2,1,2,1,2],[0,1,'I',2,1,2,1,2]]
 for q,(op,reg,*targets) in enumerate(PROGRAM,1):
  p=PRIMES[reg]
  if op=='I':e.append([q,targets[0]+1,'I',p,1,p,1,p])
  else:
   e.append([q,targets[0]+1,op,p,p,1 if op=='D' else p,p,1 if op=='D' else p])
   e.append([q,targets[1]+1,'Z',p,p,p,1,1])
 return e
def expected_word(codes,edges,end):
 cs=[codes[e[end]] for e in edges]
 return {():-sum(cs),**{(f'edge{i}_hat',):c for i,c in enumerate(cs) if c}}
def fresh_degree(rows):
 d=defs(rows);free=closure(d,[OUT])-set(d)
 def propagate(correct=False):
  w={n:1 for n in free}
  for n,o,a,b in rows:
   x,y=[0 if type(v)is int else w[v] for v in [a,b]]
   w[n]=x+y if o=='*' else max(x,y)
   if correct and n=='native__R15':w[n]=827
  return w
 raw=propagate();names=['native__wn2','native__R12','native__R10a','native__gam'];X,a,c,G=names
 p=poly(rows,'native__R15',names)
 expected={tuple(sorted(m)):v for m,v in [((X,X),1),((X,a,c),2),((X,G),2),((a,c,G),2),((G,G),1),((a,c,c),-4),((c,c),-3)]}
 ck(p==expected,'actual native cancellation')
 ck([raw[n] for n in names]==[312,379,68,380],'actual native cut degrees')
 ck(max(sum(raw[n] for n in m) for m in p)==827,'native factor bound')
 guarded=propagate(True)
 ck((raw[OUT],guarded[OUT],guarded['sparse_all_units'],guarded['norm_sum5'],guarded['norm_residual1'])==(5227,5160,5062,98,3),'full degree propagation')
 return dict(uniform_upper=5160,syntactic_upper=5227,native_product=5062,SOS=98,control=3,main_norm=plist(p),boundary_degrees={n:raw[n] for n in names},exact_degree_claimed=False)
def build(root,author):
 for n,h in AUTHOR.items():ck(sha((author/n).read_bytes())==h,'author pin '+n)
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'parent pin '+n)
 rec=read(author/'residue_affine_sparse_recoded467.json');oldrec=read(root/'residue_affine_sparse_shared470.json')
 ck(rec['source_sha256']==AUTHOR['residue_affine_sparse_recoded467.py'] and rec['dependencies']==PINS,'author binding')
 ck(oldrec['source_sha256']==PINS['residue_affine_sparse_shared470.py'],'parent helper binding')
 oldp,newp=oldrec['packet'],rec['packet'];before=enc(oldrec);old,new=oldp['source'],newp['source'];od,nd=defs(old),defs(new)
 for p in [oldp,newp]:ck(p['source_sha256']==sha(enc(p['source'])),'array binding')
 for k in ['parameters','fixed_program_parameters','witnesses','output','literal_height_radix_rows']:
  ck(oldp[k]==newp[k],'same interface '+k)
 ck(newp['ordinary_input_parameter']=='input'==oldp['parameters'][-1],'explicit ordinary input')
 free=oldp['parameters']+oldp['witnesses'];ck(len(free)==70 and len(oldp['witnesses'])==67,'ports')
 ck(oldp['parameters']==['program','radix_program','input'] and oldp['fixed_program_parameters']==['program','radix_program'],'two fixed parameters')
 ck(audit(old,free)==dict(total=470,M=175,A=295),'old complete ledger')
 ck(audit(new,free)==dict(total=467,M=171,A=296),'new complete ledger')
 base=closure(od,['sparse_all_units']+[f'norm_residual{i}' for i in [0,2,3,4,5]])&set(od)
 ck(len(base)==388 and set(rec['source_recipe']['base_names'])==base,'independent pre-control closure')
 def rename(x):return 'recode_'+x[1:] if type(x)is str and x.startswith('r') and x[1:].isdigit() else x
 newdefs={f'recode_{i}':[f'recode_{i}',o,rename(a),rename(b)] for i,o,a,b in SPEC}
 ck(len(newdefs)==64,'all64 paid recode rows')
 expected={n:od[n][:] for n in base}
 expected.update(newdefs)
 final_names={r[0] for r in old[-20:]};expected.update({r[0]:r[:] for r in old[-20:]})
 expected['norm_residual1']=['norm_residual1','-','recode_62','recode_64']
 ck(nd==expected,'independent complete array reconstruction')
 ck(ledger([r for r in new if r[0] not in final_names])==dict(total=447,M=164,A=283),'certificate447')
 ck(ledger([r for r in new if r[0] in final_names])==dict(total=20,M=7,A=13),'finalizer20')
 ck(len(final_names&base)==5,'five noncontrol residuals in base')
 retained=set(nd)&set(od);ck(len(retained)==403,'literal retained names')
 ck(all(nd[n]==od[n] for n in retained if n!='norm_residual1'),'all other retained definitions literal')
 native={n for n in od if n.startswith('native__')};ck(len(native)==72 and native<=base,'native72 in precontrol base')
 height=[['height_85','+','input','height_slack'],['radix_86','*','radix_program','height_85']]
 transport=[['transport_left_282','+','shift_payload_281','program'],['transport_right_284','+','current_155','final_payload_scaled_283'],['norm_residual2','-','transport_left_282','transport_right_284']]
 for row in height+transport:ck(od[row[0]]==nd[row[0]]==row,'actual input/radix/transport')
 for i in range(36):ck(nd[f'edge_{i}']==[f'edge_{i}','-',f'edge{i}_hat',1],'actual hat interpretation')
 f=read(root/'residue_affine_sparse_factored.json');e=build_edges()
 ck(f['default_table']==PROGRAM and f['default_primes']==PRIMES and f['edges']==e,'literal U21 table and edges')
 ck(rec['literal_edges']==e and rec['literal_program']==PROGRAM and rec['literal_primes']==PRIMES,'author table match')
 cc=read(root/'residue_affine_sparse_control_codes.json')['state_codes']
 ck([cc[str(i)] for i in range(23)]==OLDCODES==rec['old_state_codes'],'old code authentication')
 weight={2:0,3:1,5:2,7:3,11:8,13:9,17:17,19:11};corr={9:1,11:16,12:32,13:32,14:1,18:16}
 rebuilt=[0]+[weight[PRIMES[t[1]]]+4*(t[0]=='I')+corr.get(q,0) for q,t in enumerate(PROGRAM,1)]+[14]
 ck(rebuilt==NEWCODES==rec['new_state_codes'] and len(set(rebuilt))==23 and max(rebuilt)==41,'injective bounded new codes')
 hats={f'edge{i}_hat' for i in range(36)};words=[]
 for rows,cn,nn,cs in [(old,'control_codes__current_positive_29','control_codes__target_difference_70',OLDCODES),(new,'recode_23','recode_61',NEWCODES)]:
  for n,end in [(cn,0),(nn,1)]:
   p=poly(rows,n,hats);ck(p==expected_word(cs,e,end),'complete actual-hat control expansion')
   words.append(dict(register=n,polynomial=plist(p)))
 # Expand each new affine intermediate at the genuine supplied hats. The last
 # three rows are separately bound to the actual B/P, not independent guesses.
 affine=[]
 for n in newdefs:
  if int(n.split('_')[1])<62:
   p=poly(new,n,hats);ck(all(len(m)<=1 for m in p),'affine control producer')
   affine.append(dict(register=n,terms=plist(p)))
 for cs in [OLDCODES,NEWCODES]:
  ck(cs[0]==0 and all(0<cs[q]<128 for q in range(1,23)),'initial/end code guards at h2')
  ck(all((cs[i]==cs[j])==(i==j) for i in range(23) for j in range(23)),'all529 adjacency comparisons')
 # This whole-output expansion is independent of the author's finalizer token
 # proof: control residuals expand through B/P to all36 actual supplied hats.
 U='sparse_all_units';other=[f'norm_residual{i}' for i in [0,2,3,4,5]]
 cuts=hats|{U,'radix_86','scale_89'}|set(other)
 pcold=poly(old,'norm_residual1',cuts);pcnew=poly(new,'norm_residual1',cuts)
 B={('radix_86',):1};P={('scale_89',):1}
 for got,cs in [(pcold,OLDCODES),(pcnew,NEWCODES)]:
  want=add(add(mul(B,expected_word(cs,e,1)),expected_word(cs,e,0),-1),{('scale_89',):cs[22]},-1)
  ck(got==want,'literal control transport factor')
 outold=poly(old,OUT,cuts);outnew=poly(new,OUT,cuts)
 delta=mul({(U,):1},add(mul(pcnew,pcnew),mul(pcold,pcold),-1))
 ck(add(outnew,outold,-1)==delta,'actual expanded full correction identity')
 for rows in [old,new]:
  p=poly(rows,OUT,{U}|{f'norm_residual{i}' for i in range(6)})
  want={():-1,(U,):1,**{tuple(sorted([U,f'norm_residual{i}',f'norm_residual{i}'])):1 for i in range(6)}}
  ck(p==want,'full positive integer finalizer')
 # Prove compact deltas at the actual raw-edge cuts, then verify actual hats.
 raw={f'edge_{i}' for i in range(36)}
 dc=add(poly(new,'recode_23',raw),poly(old,'control_codes__current_positive_29',raw),-1)
 dn=add(poly(new,'recode_61',raw),poly(old,'control_codes__target_difference_70',raw),-1)
 wantdc=add(poly(old,'prime_selector_115',raw),{('edge_24',):47,('edge_25',):47},-1)
 ck(dc==wantdc and dn=={('edge_2',):1,('edge_10',):1,('edge_20',):-47,('edge_31',):-49},'compact changes')
 ck(nd['recode_14']==['recode_14','+','u21_grouped_J_0','prime_selector_95'],'paid population reuse')
 degree=fresh_degree(new);ck(enc(oldrec)==before,'untouched actual470 packet')
 return dict(status='PASS_INDEPENDENT_DIRECT_RECODED467',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PINS,
  complete_source_sha256=sha(enc(new)),ledger=ledger(new),certificate=ledger([r for r in new if r[0] not in final_names]),
  witnesses=67,free_ports=70,all_rows_and_ports_live=True,retained_definitions_literal_except_control=402,
  precontrol_base=388,new_control_rows=64,native_literal=72,finalizer_rows=20,unchanged_finalizer_definitions=19,
  edges=e,new_codes=NEWCODES,old_codes=OLDCODES,code_maximum=41,minimum_valid_B=128,
  four_control_words=words,all61_affine_new_intermediates=affine,full_output_correction_terms=len(delta),full_output_correction_digest=sha(enc(plist(delta))),
  current_delta=plist(dc),next_delta=plist(dn),degree=degree,
  scope=dict(all_ring_correction=True,positive_integer_zero_map='identity on all supplied ports on valid fixed E/C slices',
   precontrol_bootstrap='inherited unchanged from504; proof cross-read separately',one_program_map_claimed=False,
   predecessor_execution=False,native_zero_materialized=False,new_numeric_fixture=False))
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=p.parse_args();r=build(a.root,a.author_root or a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact independent receipt')
 print(r['status'],'467 rows; identical positive zero tuples; uniform degree <=5160')
if __name__=='__main__':main()
