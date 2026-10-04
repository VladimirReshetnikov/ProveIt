#!/usr/bin/env python3
"""Independent data-only coefficient and complete-source audit."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
AUTHOR={
 'matrix193_structured_coefficient_scout.py':'39ab5c942af5bd6d725d2c17e89d2222e3e44bf26cc59e3c1bad1d4e011e10a9',
 'matrix193_structured_coefficient_scout.json':'ebdc03c29dc9469896aa858312c95400a77adf853116e6819c514fb4e587d032',
 'matrix193_structured_coefficient_scout.md':'8e49bed183eed196768951d3a86febc6cbd8d0a2e8898387c41b3b0e0ebeced3'}
PARENTS={
 'matrix193_balanced_output_scout.py':'e567a5be0cb656dfc984aa86fb306584dd837b7c24568659af222c781266d76a',
 'matrix193_balanced_output_scout.json':'63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf',
 'matrix193_balanced_output_scout.md':'cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde',
 'matrix193_gamma1_recode.json':'9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742'}
def ck(t,m):
 if not t:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(path):
 def obj(items):
  d={}
  for k,v in items:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(v):raise ValueError('nonfinite JSON')
 return json.loads(path.read_text(),object_pairs_hook=obj,parse_constant=bad)
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def add(p,q,s=1):
 r=dict(p)
 for k,v in q.items():
  r[k]=r.get(k,0)+s*v
  if not r[k]:del r[k]
 return r
def mul(p,q):
 r={}
 for i,a in p.items():
  for j,b in q.items():r[i+j]=r.get(i+j,0)+a*b
 return {i:a for i,a in r.items() if a}
def constant(n):return {0:n} if n else {}
def shift(p,k):return {i+k:a for i,a in p.items()}
def matadd(a,b):return [add(x,y) for x,y in zip(a,b)]
def matmul(a,b):return [add(mul(a[2*r],b[c]),mul(a[2*r+1],b[c+2])) for r in [0,1] for c in [0,1]]
def matshift(a,k):return [shift(p,k) for p in a]
def matconst(a):return [constant(v) for v in a]
def intmul(a,b):return [a[2*r]*b[c]+a[2*r+1]*b[c+2] for r in [0,1] for c in [0,1]]
def inverse(a):
 ck(a[0]*a[3]-a[1]*a[2]==1,'determinant1');return [a[3],-a[1],-a[2],a[0]]
def upper(g):return [g['matrix'][r][c] for r in [0,1] for c in [0,1]]
def digest_object(v):return sha(json.dumps(v,sort_keys=True,separators=(',',':')).encode())
def audit_graph(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'distinct free ports');dep={};count=Counter()
 for name,op,a,b in p['source']:
  ck(name not in known and op in ['*','+','-'],'fresh operation')
  ck(all(type(v) is int or type(v) is str and v in known for v in [a,b]),'acyclic closure')
  known.add(name);dep[name]=[a,b];count[op]+=1
 todo=[p['output']];live=set()
 while todo:
  v=todo.pop()
  if type(v) is str and v not in live:live.add(v);todo.extend(dep.get(v,[]))
 ck(live==known,'every row and supplied port live')
 literals={v for row in p['source'] for v in row[2:] if type(v) is int}
 return {'rows':len(dep),'M':count['*'],'A':count['+']+count['-'],'free_ports':len(p['free']),'positive_witnesses':len(p['witnesses']),'integer_literals':len(literals),'max_literal_bits':max(abs(n).bit_length() for n in literals)}
def run(root,author_root):
 for base,pins in [(root,PARENTS),(author_root,AUTHOR)]:
  for name,pin in pins.items():ck(sha((base/name).read_bytes())==pin,'pin '+name)
 a=read(author_root/'matrix193_structured_coefficient_scout.json');p=a['packet']
 balanced=read(root/'matrix193_balanced_output_scout.json');old=balanced['packets'][1]
 raw=read(root/'matrix193_gamma1_recode.json');g=raw['packet'];letters=g['letters'];tiles=g['tiles']
 ck(a['pins']==PARENTS,'declared exact dependencies')
 gens={v['name']:v for v in g['generators']};C=upper(gens['C']);CI=inverse(C)
 def word(w):
  ans=[1,0,0,1]
  for ch in w:ans=intmul(ans,letters[ch])
  return ans
 for v in letters.values():inverse(v)
 hx=[];gy=[]
 for tile in tiles:
  h=word(tile['h']);gg=word(tile['g']);i=tile['id']
  ck(h==upper(gens['A'+str(i)]) and gg==inverse(upper(gens['B'+str(i)])),'word matches original generator')
  hx.append(intmul(intmul(CI,h),C));gy.append(gg)
 ck(len(tiles)==96,'96 original tiles')
 # Reconstruct first-appearance groups from the fixed matrices, independently of saved group records.
 groups=[]
 for kind,matrices in [('K',hx),('G',gy)]:
  where={}
  for j,matrix in enumerate(matrices):
   key=tuple(matrix)
   if key not in where:
    where[key]=len(groups);groups.append({'kind':kind,'matrix':matrix,'edges':[],'source_coordinate':0 if kind=='K' else 2})
   groups[where[key]]['edges'].append(j+2)
 load=inverse(word('0101011101010111'))
 groups += [{'kind':'LOAD','matrix':load,'edges':[0],'source_coordinate':2},old['groups'][-1]]
 ck(groups==old['groups'],'complete grouped fixed registry')
 words={side:[tiles[v['edges'][0]-2]['h' if side=='X' else 'g'] for v in groups if v['kind']==('K' if side=='X' else 'G')] for side in ['X','Y']}
 for side in ['X','Y']:
  gs=[v for v in groups if v['kind']==('K' if side=='X' else 'G')]
  for gr,w in zip(gs,words[side]):ck(all(tiles[e-2]['h' if side=='X' else 'g']==w for e in gr['edges']),'merged words agree')
  ck(words[side][:4]==list('01[]'),'copy prefix')
 ck(words['X'][-2:]==['J1','#'] and words['Y'][-5:]==['0J1','J10','1J1','J11','#'],'literal tails')
 Z=[{},{},{},{}];I=matconst([1,0,0,1]);T0,T1,L,R=[matconst(letters[c]) for c in '01[]']
 pref=matadd(matadd(matshift(T0,3),matshift(T1,2)),matadd(matshift(L,1),R))
 D01=matadd(matshift(T0,2),matshift(T1,1));rightX=matadd(D01,matmul(T0,R));rightY=matadd(D01,R);leftY=matadd(D01,L)
 coefficient_targets={};summary={};bad_left=0
 for side,count in [('X',22),('Y',29)]:
  categories=['R','L0','L1'] if side=='X' else ['R','L'];acc={cat:[{} for _ in range(4)] for cat in categories};catcount=Counter();triple_direct=Z
  for j in range(count):
   w0,w1,w2=words[side][4+3*j:7+3*j];d=3*(count-1-j)
   direct=matadd(matadd(matshift(matconst(word(w0)),2),matshift(matconst(word(w1)),1)),matconst(word(w2)))
   if w2[0]=='[':
    if side=='X':
     b=w0[-1];f=w0[:-2];ck(b in '01' and [w0,w1,w2]==[f+'0'+b,f+'1'+b,'['+f+'0'+b],'left X words');cat='L'+b
     A=matconst(word(f));Tb=matconst(letters[b]);form=matmul(matadd(matmul(A,D01),matmul(matmul(L,A),T0)),Tb)
     wrong=matmul(matadd(matmul(A,D01),matmul(matmul(A,L),T0)),Tb)
     bad_left+=int(wrong!=direct)
    else:
     f=w0[1:];ck([w0,w1,w2]==['0'+f,'1'+f,'['+f],'left Y words');cat='L';A=matconst(word(f));form=matmul(leftY,A)
   else:
    f=w0[:-1];ck([w0,w1,w2]==([f+'0',f+'1',f+'0]'] if side=='X' else [f+'0',f+'1',f+']']),'right words');cat='R';A=matconst(word(f));form=matmul(A,rightX if side=='X' else rightY)
   ck(form==direct,'each whole matrix triple identity')
   acc[cat]=matadd(acc[cat],matshift(A,d));catcount[cat]+=1;triple_direct=matadd(triple_direct,matshift(direct,d))
  if side=='X':
   triple=matmul(acc['R'],rightX)
   for bit in ['0','1']:
    A=acc['L'+bit];triple=matadd(triple,matmul(matadd(matmul(A,D01),matmul(matmul(L,A),T0)),matconst(letters[bit])))
   assembled=matadd(matadd(matshift(pref,68),matshift(triple,2)),matadd(matshift(matconst(word('J1')),1),matconst(word('#'))));matrices=[word(w) for w in words[side]]
  else:
   triple=matadd(matmul(acc['R'],rightY),matmul(leftY,acc['L']));tail=Z
   for degree,w in enumerate(reversed(words['Y'][-5:]),1):tail=matadd(tail,matshift(matconst(word(w)),degree))
   tail=matadd(tail,matconst(load));assembled=matadd(matadd(matshift(pref,93),matshift(triple,6)),tail);matrices=[word(w) for w in words[side]]+[load]
  ck(triple==triple_direct,'aggregate matrix triple identity')
  direct=Z
  for j,matrix in enumerate(matrices):direct=matadd(direct,matshift(matconst(matrix),len(matrices)-1-j))
  ck(assembled==direct,'entire matrix word polynomial')
  if side=='X':assembled=matmul(matmul(matconst(CI),assembled),matconst(C))
  rep={j:1 for j in range(len(matrices))}
  assembled[0]=add(assembled[0],rep,-1);assembled[3]=add(assembled[3],rep,-1)
  for column in [0,1]:
   coefficient_targets[(side,column)]=add({2*j+1:v for j,v in assembled[column].items()},{2*j:v for j,v in assembled[column+2].items()})
  summary[side]={'groups':len(matrices),'triples':count,'categories':dict(catcount),'full_matrix_entry_term_counts':[len(v) for v in direct]}
 ck(bad_left==12,'all twelve left boundaries detect wrong commutation')
 # Sparse interpretation of every pure-Q source row, including all 638 new rows.
 Q=old['ports']['Q'];env={Q:{1:1}}
 for name,op,l,r in p['source']:
  if name==Q:continue
  if all(type(v) is int or v in env for v in [l,r]):
   aa=constant(l) if type(l) is int else env[l];bb=constant(r) if type(r) is int else env[r]
   env[name]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
 ck(all(row[0] in env for row in p['coefficient_component']),'every component row is a fixed integer Q polynomial')
 certificates=[];repl={}
 for block in old['extraction']:
  side=block['side']
  for column,pr in enumerate(block['products']):
   name=pr['polynomial'];target=coefficient_targets[(side,column)];dense=[target.get(k,0) for k in range(max(target)+1)]
   ck(dense==list(reversed(pr['coefficients'])),'original matrix coefficients match parent')
   new=p['replacement'][name];ck(env[new]==target,'entire independently emitted coefficient cut')
   repl[name]=new;certificates.append({'side':side,'column':column,'old':name,'new':new,'degree':len(dense)-1,'ascending_coefficients':dense,'coefficient_count':len(target)})
 ck(len(repl)==4 and repl==p['replacement'],'four complete cuts')
 # Pay and identify the inherited R98-to-R97 subtraction directly in actual rows.
 rep98={2*j:1 for j in range(98)};rep97={2*j:1 for j in range(97)}
 subtractors=[]
 for name,op,l,r in p['coefficient_component']:
  if op=='-' and type(l) is str and type(r) is str and env.get(l)==rep98 and env.get(r)=={194:1}:
   ck(env[name]==rep97,'paid R97');subtractors.append([name,l,r])
 ck(len(subtractors)==1,'exact paid R97 subtraction')
 oldnames={row[0] for row in old['source']};newnames={row[0] for row in p['source']};removed=oldnames-newnames
 ck(removed==set(p['removed_parent_rows']) and len(removed)==1344,'exact deleted rows')
 added=[row for row in p['source'] if row[0] not in oldnames];ck(added==p['coefficient_component'] and len(added)==638,'exact 638 replacement rows')
 insert=old['stage_counts']['packing']+old['stage_counts']['native'];expected=[]
 for j,row in enumerate(old['source']):
  if j==insert:expected.extend(added)
  name,op,l,r=row
  if name in removed:continue
  ck(all(v not in removed or v in repl for v in [l,r]),'deleted cone has no unaccounted outside use')
  expected.append([name,op,repl.get(l,l),repl.get(r,r)])
 ck(expected==p['source'],'entire source equals literal proved-cut substitution')
 for key in ['free','fixed_numerals','witnesses','output','ports','native_cut_bindings','comparisons','fixture_fixed_bindings']:
  ck(exact(p[key],old[key]),'unchanged full interface '+key)
 expected_extract=read(root/'matrix193_balanced_output_scout.json')['packets'][1]['extraction']
 for block in expected_extract:
  for pr in block['products']:pr['polynomial']=repl[pr['polynomial']]
 ck(exact(p['extraction'],expected_extract),'all extraction metadata matches literal substitution')
 current=audit_graph(p);parent=audit_graph(old);diagnostic=audit_graph(a['diagnostic_unchanged'])
 ck(exact(a['diagnostic_unchanged'],balanced['packets'][0]),'complete diagnostic unchanged')
 removed_counts=Counter(row[1] for row in old['source'] if row[0] in removed);added_counts=Counter(row[1] for row in added)
 ck(current['rows']==1756 and current['M']==795 and current['A']==961 and current['positive_witnesses']==150,'actual ledger')
 ck(removed_counts['*']==672 and removed_counts['+']+removed_counts['-']==672,'deleted ledger')
 ck(added_counts['*']==343 and added_counts['+']+added_counts['-']==295,'inserted ledger')
 ck(p['ledger']['degree']==35587 and a['inherited_degree']['exact']==35587,'degree inherited by complete polynomial identity')
 return {'status':'PASS','review_source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR,'inert_parent_pins':PARENTS,
  'word_matrix_formulas':summary,'literal_left_boundary_counterchecks':bad_left,'original_tile_pair_products':96,'full_coefficient_certificates':certificates,
  'all_component_rows_interpreted':len(added),'R97_subtraction_rows':subtractors,'surrounding_source':{'identical_retained_rows':len(old['source'])-len(removed),'deleted_M':removed_counts['*'],'deleted_A':removed_counts['+']+removed_counts['-'],'added_M':added_counts['*'],'added_A':added_counts['+']+added_counts['-'],'whole_array_reconstructed_literally':True,'full_polynomial_identity':'integer coefficient identities followed by literal substitution; hence all commutative rings'},
  'actual_ledger':current,'parent_ledger':parent,'diagnostic_ledger':diagnostic,'degree_inheritance':{'actual':35587,'diagnostic':1363,'new_degree_experiment':False},
  'full_source_sha256':digest_object(p['source']),'scope':'No author/predecessor Python executed or imported; no native history theorem recertification or new accepting fixture; full source coefficient identity preserves all supplied tuples.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path)
 args=ap.parse_args();result=run(args.root,args.author_root or args.root)
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(exact(result,read(args.expect)),'type-exact independent receipt replay')
 print(json.dumps({'status':result['status'],'actual':result['actual_ledger'],'coefficient_rows':result['all_component_rows_interpreted'],'degree':result['degree_inheritance']},sort_keys=True))
if __name__=='__main__':main()
