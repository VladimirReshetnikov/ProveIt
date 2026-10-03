"""Independent depth-two coverage and complete-circuit review.

Reuses the authenticated independent single-move review engine, not author
Graph/moves/seed_graphs. Author byte-serialization digests have a separate scope.
"""
import argparse,ast,hashlib,json,random,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
SUBJECT={'complete86_two_move_scout.py':'0956d01e6cc3360832d6c9da71c74e6e36ef1d7c681fbaf0c97eb5d93528f352','complete86_two_move_scout.json':'be3f79da5d11519638cac7d203704ef3268d85e555667baee4fdea0a00a59855','complete86_two_move_scout.md':'86ebc6f5cd84087f4e5d7ef7008a87ce76298591642804a54a5f148a530e4ec6'}
ENGINE={'review_complete86_affine_port_scout.py':'12311ac00d0cc039edc9949a8046b3342f329a49263ec61d8929c93451784e0b'}
PINS={
 'complete86_affine_port_scout.py':'5abbc4ee9b44f83bf9d96b0e54f6d4ebe6c1fd461637fdd915ae71465a867e2c',
 'complete86_affine_port_scout.json':'114301fbfdb40857b7e139a4ffa132c64b45a5f56d000b6d15a8893c57e5c7c1',
 'complete86_affine_port_scout.md':'295dc976c0cffb71fe17be53c6bd541431fc7bb4d43a2f81e9f61c426b3cc558',
 'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
 'complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
 'complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
}
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def canonical(obj):return json.dumps(obj,sort_keys=True,separators=(',',':'),allow_nan=False)
def digest(obj):return sha(canonical(obj).encode())
def auth(root,pins):
 out={}
 for name,pin in pins.items():
  b=(Path(root)/name).read_bytes();need(sha(b)==pin,'Strict pin '+name);out[name]=b
 return out

def verify(root,subject_root):
 root,subject_root=Path(root),Path(subject_root);need(len(SUBJECT)==3,'Frozen subject trio required');subject=auth(subject_root,SUBJECT);deps=auth(root,PINS);engine=auth(root,ENGINE)
 tree=ast.parse(subject['complete86_two_move_scout.py']);source_pins=next(ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='PINS'for t in n.targets));need(source_pins==PINS,'Exact author dependency boundary')
 saved=json.loads(subject['complete86_two_move_scout.json']);need(saved['pins']==PINS and saved['source_sha256']==SUBJECT['complete86_two_move_scout.py'],'Subject source/receipt lineage')
 # Compile only the previous independent review after authenticating its
 # bytes. Its main/verify are never called; no pycache or historical suite.
 namespace={'__name__':'_authenticated_independent_affine_review','__file__':str(root/'review_complete86_affine_port_scout.py')};exec(compile(engine['review_complete86_affine_port_scout.py'],namespace['__file__'],'exec'),namespace)
 old=json.loads(deps['complete86_factored_first_root.json'])['forms'][0];need(old['normalized']is True,'Actual normalized parent')
 g=namespace['Algebra']();env=g.parse(old['source']);out=env['polynomial'];baseline=g.emit(out);namespace['validate'](baseline);need((baseline['M'],baseline['A'])==(48,38),'Literal baseline86')
 original_free=old['witnesses']+old['ledger']['fixed_numerals']+['x'];need(set(baseline['free_ports'])==set(original_free)and len(original_free)==26,'Exact nineteen witness/six numeral/one ordinary ports')
 a,b,h=env['D1'],env['exponent_partial'],env['a4m5'];rho,sigma=g.leaf('rho'),g.leaf('sigma');u=g.op('*',rho,h);v=g.op('*',sigma,h);joint=g.op('*',g.op('+',rho,sigma),h);mu=g.op('+',b,u)
 roots=[('original',g.op('+',a,joint),mu),('distributed_left',g.op('+',g.op('+',a,u),v),mu),('distributed_right',g.op('+',a,g.op('+',u,v)),mu),('through_input_left',g.op('+',g.op('+',mu,g.op('-',a,b)),v),mu),('through_input_right',g.op('+',mu,g.op('+',g.op('-',a,b),v)),mu),('recover_rho_product',g.op('+',a,joint),g.op('+',b,g.op('-',joint,v)))]
 first=set();first_proofs=set();raw_first=0;first_kinds=Counter()
 for name,main,inputroot in roots:
  for left,right in((env['R14'],main),(env['exponent_rhs'],inputroot)):g.prove(left,right,(a,b,h,rho,sigma))
  seed=g.replace(out,{left:right for left,right in((env['R14'],main),(env['exponent_rhs'],inputroot))if left!=right});first.add(seed)
  for kind,left,right,cuts in list(namespace['candidates'](g,seed)):
   g.prove(left,right,cuts);first_proofs.add((left,right,tuple(sorted(set(cuts)))));first.add(g.replace(seed,{left:right}));raw_first+=1;first_kinds[kind]+=1
 frozen_one=json.loads(deps['complete86_affine_port_scout.json']);need(len(first)==frozen_one['distinct_complete_sources_across_seeds']==874 and raw_first==frozen_one['raw_generated_moves']==1300,'Entire first layer independently reproduced')
 seen=set(first);costs=Counter();ledgers=Counter();paid=0;first_costs=Counter();minimum_roots=[]
 def charge(node,first_layer=False):
  nonlocal paid
  p=g.emit(node);namespace['validate'](p);need(set(p['free_ports'])==set(original_free),'Exact complete source interface at every candidate');costs[p['operations']]+=1;ledgers[p['M'],p['A']]+=1;paid+=p['operations']
  if first_layer:first_costs[p['operations']]+=1
  if p['operations']==86:minimum_roots.append(node)
 for node in first:charge(node,True)
 second_proofs=set();raw_second=0;second_kinds=Counter()
 for node in sorted(first):
  for kind,left,right,cuts in list(namespace['candidates'](g,node)):
   raw_second+=1;second_kinds[kind]+=1;key=(left,right,tuple(sorted(set(cuts))))
   if key not in second_proofs:g.prove(left,right,cuts);second_proofs.add(key)
   result=g.replace(node,{left:right})
   if result not in seen:seen.add(result);charge(result)
 expected_counts=dict(seed_cut_proofs=12,first_layer_complete_sources=len(first),first_move_instances=raw_first,second_move_instances=raw_second,distinct_second_cut_proofs=len(second_proofs),distinct_all_local_cut_proofs=len(first_proofs|second_proofs),distinct_complete_sources=len(seen),literal_gates_checked=paid,full_numeric_checks=2*len(seen),signed_checks=len(seen),rational_checks=len(seen))
 # The numerical-check totals here are author execution claims audited from
 # the source loop. They are not represented as this review's own replays.
 need(saved['counts']==expected_counts,'Complete author census/proof/loop counts match')
 ledger_table=[dict(M=m,A=a,sources=n)for(m,a),n in sorted(ledgers.items())];hist={str(k):v for k,v in sorted(costs.items())};need(saved['ledger_histogram']==ledger_table and saved['cost_histogram']==hist,'Every independent paid histogram cell matches')
 minimum=min(costs);need(minimum==saved['minimum']==86 and costs[minimum]==saved['minimum_sources']==2661,'Exact bounded minimum')
 need(saved['grammar']['seed_names']==[n for n,_,_ in roots]and saved['grammar']['maximum_local_moves']==2 and saved['grammar']['new_coordinates']is False and saved['grammar']['historical_verify_called']is False,'Correct finite grammar/domain metadata')
 need(saved['parent']==dict(operations=86,M=48,A=38,witnesses=19,exact_degree=179,ordinary_input='x'),'Inherited parent statement')
 # Independently parse every saved full representative into the independent
 # universe. Numeric evaluation of these representatives is supplemental.
 reps=saved['representatives_by_ledger'];need(len(reps)==len(ledgers),'One full representative per paid ledger')
 rng=random.Random(8622026);assignments=[]
 for case in range(4):
  val={name:rng.randint(1,5)for name in baseline['free_ports']};val.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19)
  if case==1:val={n:-v if j%3==0 else v for j,(n,v)in enumerate(val.items())}
  if case>=2:val={n:Fraction(v,3 if case==2 else 7)for n,v in val.items()}
  assignments.append(val)
 answers=[namespace['evaluate'](baseline,val)for val in assignments];need(any(ans!=-1 for ans in answers),'At least one nontrivial full-product numerical fixture')
 representative_rows=[];rep_keys=set();full_outputs=0;rep_gates=0
 for rep in reps:
  p=rep['packet'];namespace['validate'](p);root_node=g.parse(p['source'])[p['output']];need(root_node in seen,'Saved entire representative is independently enumerated');key=(p['M'],p['A']);need(key in ledgers and key not in rep_keys,'Distinct represented paid ledger');rep_keys.add(key)
  need(rep['source_sha256']==digest(p),'Representative literal byte-format hash');need(len(rep['route']['moves'])<=2 and rep['route']['seed']in[n for n,_,_ in roots],'Representative declared route boundary')
  for val,answer in zip(assignments,answers):need(namespace['evaluate'](p,val)==answer,'Representative full signed/rational output');full_outputs+=1
  rep_gates+=p['operations'];representative_rows.append(dict(M=p['M'],A=p['A'],operations=p['operations'],independent_graph_fingerprint=g.fingerprints[root_node],author_source_sha256=rep['source_sha256']))
 pareto=[(m,a)for m,a in sorted(ledgers)if not any(mm<=m and aa<=a and(mm<m or aa<a)for mm,aa in ledgers)];need(pareto==[(48,38)],'Exact finite M/A frontier')
 need([(f['packet']['M'],f['packet']['A'])for f in saved['multiplication_addition_frontier']]==pareto,'Saved frontier matches')
 for f in saved['multiplication_addition_frontier']:
  need(g.parse(f['packet']['source'])[f['packet']['output']]in seen and f['source_sha256']==digest(f['packet']),'Saved frontier whole source')
 hashes=saved['minimum_source_hashes'];need(len(hashes)==len(set(hashes))==costs[86]and hashes==sorted(hashes)and all(type(v)is str and len(v)==64 and all(c in'0123456789abcdef'for c in v)for v in hashes),'Author minimum hash-list shape and cardinality')
 need(next(r['source_sha256']for r in reps if r['packet']['operations']==86)in hashes,'Saved minimum representative included')
 for key in('first_layer_source_set_sha256','complete_source_set_sha256','ordered_census_sha256','per_first_source_new_counts_sha256'):
  value=saved[key];need(type(value)is str and len(value)==64 and all(c in'0123456789abcdef'for c in value),'Author census digest format')
 # The exact search is independent, but its structural fingerprint ordering
 # intentionally differs from the author's allocation-ID serialization.
 fingerprint_set=digest(sorted(g.fingerprints[node]for node in seen));best_set=digest(sorted(g.fingerprints[node]for node in minimum_roots))
 with tempfile.TemporaryDirectory(prefix='two_move_review_pins_')as tmp:
  for n,b in subject.items():(Path(tmp)/n).write_bytes(b)
  for n,b in subject.items():
   (Path(tmp)/n).write_bytes(b+b' ')
   try:auth(tmp,SUBJECT)
   except ValueError:pass
   else:raise AssertionError('Changed subject pin accepted')
   (Path(tmp)/n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized interpreter rejected')
 return dict(status='PASS_INDEPENDENT_COMPLETE86_TWO_MOVE_SCOUT',review_source_sha256=sha(Path(__file__).read_bytes()),subject_pins=SUBJECT,dependency_pins=PINS,independent_engine_pin=ENGINE,
  own_counts=dict(seed_cut_proofs=12,first_move_occurrences=raw_first,distinct_first_local_cuts=len(first_proofs),first_layer_sources=len(first),second_move_occurrences=raw_second,distinct_second_local_cuts=len(second_proofs),distinct_all_local_cuts=len(first_proofs|second_proofs),complete_sources=len(seen),live_paid_gates=paid,representative_sources=len(reps),representative_gates=rep_gates,representative_numeric_outputs=full_outputs,representative_rational_outputs=2*len(reps),subject_pin_rejections=3,optimized_rejections=1),
  first_cost_histogram={str(k):v for k,v in sorted(first_costs.items())},first_move_kinds=dict(sorted(first_kinds.items())),second_move_kinds=dict(sorted(second_kinds.items())),cost_histogram=hist,ledger_histogram=ledger_table,minimum=minimum,minimum_sources=costs[minimum],finite_M_A_frontier=[list(p)for p in pareto],independent_complete_graph_set_sha256=fingerprint_set,independent_minimum_graph_set_sha256=best_set,representatives=representative_rows,
  author_loop_numeric_claims=dict(signed=saved['counts']['signed_checks'],rational=saved['counts']['rational_checks'],independently_replayed_all=False),
  byte_digest_scope='Author allocation-ID source serializations and their whole-census digests are authenticated source/receipt results. This reviewer independently enumerates the complete semantic DAG family using a different commutative operand ordering, matches all counts and histograms, and verifies every saved representative. It does not claim independently reproducing the author byte hashes for all66673 sources.',
  scope='Exactly zero/one/two local moves after six pinned root schedules. Every local cut is an all-value coefficient identity, hence composition and replacement preserve the full complete polynomial. All26 supplied ports and19 witness domains are unchanged. Bounded negative result only; no unrestricted lower bound, no new universal operation claim, no historical suite.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--subject-root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.subject_root)
 if a.expect:need(canonical(r)==canonical(json.loads(a.expect.read_text())),'Exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(r['status'],r['own_counts']);print(r['cost_histogram'])
if __name__=='__main__':main()
