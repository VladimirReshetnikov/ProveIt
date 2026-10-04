#!/usr/bin/env python3
"""Fresh positive terminal-carry chart with raw dots and negative high quotients."""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={'matrix193_grouped_power_composition.py': '3facf356824eb762575e1b90bc2ad24812187f675e02406041408686a58b8a7e', 'matrix193_grouped_power_composition.json': '67ec3453bb211f3129f27d4194084007c0e1e74410745a11c4181c79ae707002', 'matrix193_grouped_power_composition.md': '66b145ba5d2c87ff3ca5cadee3a1f27de626d11315809ec18a181a88815a0d14', 'matrix193_entry_controller_charts.json': 'd5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571', 'matrix193_balanced_output_scout.md': 'cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde', 'matrix193_bounded_high_output.md': '7f5a5bab9bff8518881a16a7c9d32916ce4ca1ff9dcbaa18f7fab7d452da654c', 'matrix193_atomic_context_packing.md': 'b19f3a7188eac22055323ecc277522e18d68f0818c6f5d2da3a05ceea94262ca', 'matrix193_positive_controller_charts.md': 'e7fda47c1c60c168d65307edb78b77709b0b24c10827ace85d2e6b82e752f53c', 'matrix193_idle_free_scout.md': '3502c8c69642ab3c90e5973a3668c896b34c23c0fdb88686338853573ac236d6'}
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(s):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def add(a,b,s=1):
 d=dict(a)
 for i,c in b.items():
  d[i]=d.get(i,0)+s*c
  if not d[i]:del d[i]
 return d
def mul(a,b):
 d={}
 for i,c in a.items():
  for j,h in b.items():d[i+j]=d.get(i+j,0)+c*h
 return {i:c for i,c in d.items() if c}
def polynomials(rows,Q):
 values={Q:{1:1}}
 for n,o,a,b in rows:
  if n==Q or not all(type(v)is int or v in values for v in [a,b]):continue
  aa=({0:a} if a else {}) if type(a)is int else values[a];bb=({0:b} if b else {}) if type(b)is int else values[b]
  values[n]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
 return values

def live_names(rows,output):
 by={r[0]:r for r in rows};live=set();todo=[output]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:
   live.add(v)
   if v in by:todo.extend(by[v][2:])
 return live

def audit(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique free ports');ct=Counter();degree={n:0 if n in p['fixed_numerals'] else 1 for n in p['free']}
 for n,o,a,b in p['source']:
  ck(type(n)is str and n not in known and o in ['+','-','*'],'unique arithmetic producer')
  ck(all(type(v)is int or (type(v)is str and v in known) for v in [a,b]),'complete topological order')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0;degree[n]=da+db if o=='*' else max(da,db);known.add(n);ct[o]+=1
 ck(live_names(p['source'],p['output'])==known,'all rows/ports live')
 return {'total':len(p['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses']),'supplied_ports':len(p['free']),'fixed_coefficient_ports':len(p['fixed_numerals']),'integer_literals':len({v for r in p['source'] for v in r[2:] if type(v)is int}),'syntactic_degree_upper':degree[p['output']],'all_live':True}

def evaluate(p,values,prime):
 env=dict(values)
 for n,o,a,b in p['source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=(a*b if o=='*' else a+b if o=='+' else a-b)%prime
 return env

C=9903520314283042199192993792
# stem,dot,high,high-product,middle,bound-producer,bound-residual,extraction,history,half-low,T,product
RECIPES=[
 ['X_dot0','r1185','r1187','r1190','r1191','r1195','r2334','r2330','r2356','r898','r1189','r1188'],
 ['X_dot1','r1482','r1484','r1486','r1487','r1491','r2340','r2336','r2358','r898','r1189','r1485'],
 ['Y_dot0','r1883','r1885','r1888','r1889','r1893','r2348','r2344','r2360','r1496','r1887','r1886'],
 ['Y_dot1','r2280','r2282','r2284','r2285','r2289','r2354','r2350','r2362','r1496','r1887','r2283']]

def multivar_identity(parent,child,m,records,parent_final,child_final):
 def w(n):return m.get(n,n)
 variables={}
 def atom(name):
  if name not in variables:variables[name]=len(variables)
  return {(variables[name],):1}
 def num(x):return {():x} if x else {}
 def plus(a,b,sign=1):
  d=dict(a)
  for k,v in b.items():
   d[k]=d.get(k,0)+sign*v
   if not d[k]:del d[k]
  return d
 def times(a,b):
  d={}
  for j,c in a.items():
   for k,e in b.items():
    n=tuple(sorted(j+k));d[n]=d.get(n,0)+c*e
  return {k:v for k,v in d.items() if v}
 P=atom('cut:'+w('r107'));B=atom('cut:'+w('r3'));K=atom('formal_common_carry')
 Q=times(num(C),P);half=times(num(C//2),P)
 parent_inputs={n:atom('port:'+n) for n in parent['free']};child_inputs={n:parent_inputs[n] for n in child['free'] if n in parent_inputs}
 for r in records:
  child_inputs[r['raw_port']]=plus(plus(parent_inputs[r['old_dot_port']],half,-1),times(K,Q))
  child_inputs[r['high_port']]=plus(plus(K,parent_inputs[r['old_high_port']],-1),atom('cut:'+r['half_low']))
 for n in ['F_even','F_odd']:child_inputs[n]=plus(parent_inputs[n],times(times(num(C),B),K))
 old_seeds={r[k] for r in records for k in ['old_dot_port','old_high_port','old_slack_port']}|{'F_even','F_odd'}
 new_seeds={r[k] for r in records for k in ['raw_port','high_port']}|{'F_even','F_odd'}
 def run(p,inputs,seeds,final):
  env=dict(inputs);affected=set(seeds);forced={r[0] for r in final}
  for n,o,a,b in p['source']:
   if n==w('r108'):env[n]=Q;continue
   if n==w('r109'):env[n]=half;continue
   touched=a in affected or b in affected
   if touched:affected.add(n)
   if touched or n in forced:
    x=env[a] if type(a)is str else num(a);y=env[b] if type(b)is str else num(b)
    env[n]=times(x,y) if o=='*' else plus(x,y,1 if o=='+' else -1)
   else:env[n]=atom('cut:'+n)
  return env
 old=run(parent,parent_inputs,old_seeds,parent_final);new=run(child,child_inputs,new_seeds,child_final)
 for n in child['retained_residual_wires']:ck(old[n]==new[n],'exact mapped retained residual '+n)
 N=w('eight_units');ck(old[N]==new[N],'same native product cut')
 loss={}
 for r in records:loss=plus(loss,times(old[r['removed_residual']],old[r['removed_residual']]))
 difference=plus(plus(new[child['output']],old[parent['output']],-1),times(old[N],loss))
 ck(not difference,'entire ring contract F_new(map)=F_parent-N*sum_removed_squares')
 return {'all_retained_residuals_equal_under_polynomial_map':True,'ring_contract':'F_new(map)=F_parent-N*sum(four removed dot-bound residuals squared)','common_carry_symbol_arbitrary_for_identity':True,'actual_Q_equals_C_times_P_and_half_equals_C_over_two_times_P':True,'expanded_parent_terms':len(old[parent['output']]),'expanded_child_terms':len(new[child['output']]),'expanded_difference_terms':len(difference)}

def degrees(p,Q,exact_polys):
 d={n:0 if n in p['fixed_numerals'] else 1 for n in p['free']}
 for n,o,a,b in p['source']:
  x=d[a] if type(a)is str else 0;y=d[b] if type(b)is str else 0;d[n]=x+y if o=='*' else max(x,y)
  if n!=Q and n in exact_polys:d[n]=max(exact_polys[n],default=0)*d[Q]
 return d

def finalizer(p,N):
 rows=p['source'];by={r[0]:r for r in rows};res=p['retained_residual_wires'];squares=[]
 for n in res:
  found=[r[0] for r in rows if r[1:]==['*',n,n]];ck(len(found)==1,'one square per residual');squares.append(found[0])
 out=by[p['output']];ck(out[1]=='-' and out[3]==1,'final subtract one');product=by[out[2]];ck(product[1]=='*' and product[2]==N,'native final product');one=by[product[3]];ck(one[1]=='+' and one[3]==1,'one plus SOS')
 sums=set()
 def walk(n):
  if n in squares:return Counter({n:1})
  r=by[n];ck(r[1]=='+' and type(r[2])is str and type(r[3])is str,'sum of residual squares');sums.add(n);return walk(r[2])+walk(r[3])
 ck(walk(one[2])==Counter(squares),'all residual squares exactly once')
 names=set(res)|set(squares)|sums|{one[0],product[0],out[0]};ck(len(names)==3*len(res)+2,'complete finalizer inventory')
 ck(all(not any(v in names for v in r[2:]) for r in rows if r[0] not in names),'finalizer private boundary')
 return [r for r in rows if r[0] in names],squares,[one[0],product[0],out[0]]

def make(parent,m,index,native_labels):
 def w(n):return m.get(n,n) if type(n)is str else n
 rows=parent['source'];by={r[0]:r for r in rows};parent_res=parent['retained_residual_wires'];oldfinal,old_squares,final_names=finalizer(parent,w('eight_units'));finalset={r[0] for r in oldfinal}
 ck(by[w('r108')]==[w('r108'),'*',C,w('r107')] and by[w('r109')]==[w('r109'),'*',C//2,w('r107')],'paid Q and half scale')
 records=[];aliases={};removed_producers=set();removed_bounds=set();port_renames={};removed_slacks=set();middles=set()
 for recipe in RECIPES:
  stem=recipe[0];dot,high,hprod,mid,bprod,bres,eres,hres,lowhalf,T,prod=map(w,recipe[1:]);oldp=stem+'_positive';oldh=stem+'_high_hat';slack=stem+'_slack';newp=stem+'_raw_positive';newh=stem+'_negative_high'
  ck(by[dot]==[dot,'-',oldp,w('r109')],'old centered dot')
  ck(by[high]==[high,'-',oldh,lowhalf],'old centered high')
  ck(by[hprod]==[hprod,'*',w('r108'),high] and by[mid]==[mid,'+',dot,hprod],'old extraction middle')
  ck(by[bprod]==[bprod,'+',oldp,slack] and by[bres]==[bres,'-',bprod,w('r108')],'old dot upper bound')
  ck([r[0] for r in rows if oldp in r[2:]]==[dot,bprod],'old dot port consumers')
  ck([r[0] for r in rows if oldh in r[2:]]==[high] and [r[0] for r in rows if slack in r[2:]]==[bprod],'old high/slack consumers')
  ck([r[0] for r in rows if high in r[2:]]==[hprod],'private high producer')
  aliases[dot]=newp;aliases[high]=newh;removed_producers.update([dot,high,bprod]);removed_bounds.add(bres);port_renames[oldp]=newp;port_renames[oldh]=newh;removed_slacks.add(slack);middles.add(mid)
  records.append({'stem':stem,'old_dot_port':oldp,'old_high_port':oldh,'old_slack_port':slack,'raw_port':newp,'high_port':newh,'dot_row':by[dot],'high_row':by[high],'bound_row':by[bprod],'removed_residual':bres,'extraction_residual':eres,'history_residual':hres,'middle':mid,'half_low':lowhalf,'T':T,'product':prod,'length':144 if stem.startswith('X') else 194})
 ck(len(removed_producers)==12 and len(removed_bounds)==4,'removed producer/bound inventory')
 ck(removed_bounds<=set(parent_res),'current residual bounds')
 child={k:parent[k] for k in ['fixed_numerals','fixture_fixed_bindings','output','variant']}
 for key in ['free','witnesses']:child[key]=[port_renames.get(n,n) for n in parent[key] if n not in removed_slacks]
 def alter(row):
  n,o,a,b=row;return [n,'-' if n in middles else o,aliases.get(a,a),aliases.get(b,b)]
 prefix=[alter(r) for r in rows if r[0] not in removed_producers and r[0] not in finalset]
 final=[];kept=[];squares=[]
 for j,n in enumerate(parent_res):
  residual,square=by[n],by[old_squares[j]]
  ck(residual[0]==n and square[1:]==['*',n,n],'literal residual/square ordering')
  if n in removed_bounds:continue
  final.extend([alter(residual),alter(square)]);kept.append(n);squares.append(square[0])
 acc=squares[0]
 for j,n in enumerate(squares[1:]):
  out='carry_sos_'+str(j);ck(out not in by and out not in parent['free'],'fresh sum wire');final.append([out,'+',acc,n]);acc=out
 plus_name,mul_name,out_name=final_names
 final.extend([[plus_name,'+',acc,1],[mul_name,'*',w('eight_units'),plus_name],[out_name,'-',mul_name,1]])
 child['source']=prefix+final;child['retained_residual_wires']=kept;newby={r[0]:r for r in child['source']}
 for r in rows:
  if r[0] not in removed_producers and r[0] not in finalset:ck(newby[r[0]]==alter(r),'every retained prefinal definition')
 for n in native_labels:ck(newby[w(n)]==by[w(n)],'native63 rows literal')
 component=parent['coefficient_component'];ck(all(newby[r[0]]==r for r in component),'coefficient553 rows literal');child['coefficient_component']=component;child['component_ledger']={'total':553,'M':305,'A':248}
 oldpoly=polynomials(rows,w('r108'));newpoly=polynomials(child['source'],w('r108'));coeffs=[]
 for rec in parent['coefficient_certificates']:
  n=rec['wire'];wanted={j:c for j,c in enumerate(rec['ascending_coefficients']) if c};ck(oldpoly[n]==newpoly[n]==wanted,'whole coefficient polynomial');coeffs.append({'wire':n,'ascending_coefficients':rec['ascending_coefficients'],'degree':max(wanted),'polynomial_sha256':sha(encode(sorted(wanted.items())))})
 child['coefficient_certificates']=coeffs
 oldledger=audit(parent);ledger=audit(child)
 ck((ledger['total'],ledger['M'],ledger['A'],ledger['positive_witnesses'])==(oldledger['total']-24,oldledger['M']-4,oldledger['A']-20,oldledger['positive_witnesses']-4),'complete24-gate4-witness delta')
 child['full_ring_contract']=multivar_identity(parent,child,m,records,oldfinal,final)
 d=degrees(child,w('r108'),newpoly);s=d[w('r108')];e=d[w('edge_hat0')];ck((s,e)==[(2,1),(3,1),(3,2),(4,2)][index],'actual Q/load degrees')
 Qpoly=newpoly;cert=[]
 for rec in records:
  l=rec['length'];ck(Qpoly[rec['T']]=={l-1:1},'paid T exact power')
  lhsdeg=d[rec['product']];rhswire=by[rec['extraction_residual']][3];rhsdeg=d[rhswire]
  ck(rhsdeg<=l*s+1,'new extraction RHS upper degree')
  cert.append({'stem':rec['stem'],'length':l,'left_degree_after_exact_Q_normalization':lhsdeg,'right_degree_upper_after_exact_Q_normalization':rhsdeg,'residual_upper_degree':d[rec['extraction_residual']]})
 leader=386*s+1+e;ck(max(d[n] for n in kept)==leader,'entire residual degree upper bound after exact pure-Q normalization')
 ys=coeffs[2:];ck([c['ascending_coefficients'][-1] for c in ys]==[-490,271],'nonzero actual Y leading coefficients')
 ck(all(c['left_degree_after_exact_Q_normalization']==leader and c['right_degree_upper_after_exact_Q_normalization']<leader for c in cert[2:]),'Y product strictly dominates RHS')
 native_degree=16986*s+67;exact_degree=native_degree+2*leader;ck(exact_degree==[35587,53345,53347,71105][index],'uniform degree derivation')
 ledger['outer_residuals']=len(kept);ledger['exact_degree']=exact_degree;child['ledger']=ledger
 child['degree_proof']={'Q_degree':s,'LOAD_degree':e,'native_degree_inherited_from_unchanged_native_polynomial':native_degree,'largest_residual_exact_degree':leader,'Y_leading_coefficients':[-490,271],'Y_leader_formula':'-a0*c0_top*LOAD_top*Q_top^386','all_residual_upper_bounds_checked_after_exact_pure_Q_polynomial_normalization':True,'extraction_bounds':cert,'full_exact_degree':exact_degree,'old_degree_not_blindly_transferred':True}
 child['chart_records']=records;child['source_boundary_checks']={'native_rows_literal':63,'coefficient_rows_literal':553,'current_residuals':len(kept),'new_finalizer_rows':len(final),'old_finalizer_explicitly_traced_through_interleaved_rows':len(oldfinal),'all_other_prefinal_rows_retained_modulo_dot_high_aliases_and_middle_sign':True}
 child['parent_reference']={'receipt':'matrix193_grouped_power_composition.json','packet_index':index,'source_array_sha256':sha(encode(rows)),'fresh_parent_ledger':oldledger}
 tests=[];rng=random.Random(1538+index)
 for prime in [1000000007,1000000009]:
  for case in range(4):
   v={n:rng.randrange(-67,68) for n in parent['free']}
   if case%2==0:v.update(parent['fixture_fixed_bindings'])
   old=evaluate(parent,v,prime);k=old[w('r1887')];values={n:v[n] for n in child['free'] if n in v}
   for rec in records:
    values[rec['raw_port']]=(v[rec['old_dot_port']]-old[w('r109')]+k*old[w('r108')])%prime
    values[rec['high_port']]=(k-v[rec['old_high_port']]+old[rec['half_low']])%prime
   for n in ['F_even','F_odd']:values[n]=(v[n]+C*old[w('r3')]*k)%prime
   new=evaluate(child,values,prime)
   for n in kept:ck(new[n]==old[n],'supplemental mapped residual')
   for n in native_labels:ck(new[w(n)]==old[w(n)],'supplemental native row')
   loss=sum(old[n]**2 for n in removed_bounds)%prime;ck(new[child['output']]==(old[parent['output']]-old[w('eight_units')]*loss)%prime,'supplemental full polynomial contract')
   tests.append({'prime':prime,'case':case,'illustrative_fixed_bindings':case%2==0,'mapped_output':new[child['output']],'removed_bound_square_sum':loss})
 child['supplemental_modular_checks']=tests
 return child

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 parent=read(root/'matrix193_grouped_power_composition.json');charts=read(root/'matrix193_entry_controller_charts.json');ck(parent['source_sha256']==PINS['matrix193_grouped_power_composition.py'],'source binding');ck(len(parent['packets'])==4 and len(charts['packets'])==3,'inventory')
 labels=[r[0] for r in parent['packets'][0]['source']];native=labels[labels.index('selection__bs_even'):labels.index('eight_units')+1];ck(len(native)==63,'native block inventory')
 packets=[make(p,{} if i==0 else charts['packets'][i-1]['map'],i,native) for i,p in enumerate(parent['packets'])]
 ck([p['ledger']['total'] for p in packets]==[1544,1541,1541,1538],'complete counts')
 ck([p['ledger']['positive_witnesses'] for p in packets]==[141,140,140,139],'new witness counts')
 return {'schema':'matrix193-terminal-carry-chart-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,'fresh_evidence':{'complete_arrays':4,'complete_rows':sum(len(p['source']) for p in packets),'exact_polynomial_map_contracts':4,'coefficient_polynomials':16,'coefficient_entries':sum(len(c['ascending_coefficients']) for p in packets for c in p['coefficient_certificates']),'supplemental_modular_maps':32},'scope':{'frozen_code_executed':False,'ordinary_input_projection_equivalent_on_valid_recipe':True,'common_witness_bijection_claim':False,'native_polynomial_unchanged':True,'degree_recomputed_after_high_shift_removal':True,'giant_accepting_fixture_or_native_tuple_emitted':False,'universal84_unchanged':True,'minimality_claim':False}}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=build(a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(exact(result,read(a.expect)),'type-exact receipt')
 print('PASS: terminal-carry arrays1544/1541/1541/1538;24 gates and4 witnesses removed;full map contracts and new degree leaders')
if __name__=='__main__':main()
