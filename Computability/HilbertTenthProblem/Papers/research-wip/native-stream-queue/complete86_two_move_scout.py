"""Complete depth-two census in the pinned affine/local rewrite grammar.

This invokes only authenticated graph/grammar primitives, not the old suite.
All candidates retain the entire polynomial and the original supplied ports.
"""
import argparse,hashlib,json,random,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
 'complete86_affine_port_scout.py':'5abbc4ee9b44f83bf9d96b0e54f6d4ebe6c1fd461637fdd915ae71465a867e2c',
 'complete86_affine_port_scout.json':'114301fbfdb40857b7e139a4ffa132c64b45a5f56d000b6d15a8893c57e5c7c1',
 'complete86_affine_port_scout.md':'295dc976c0cffb71fe17be53c6bd541431fc7bb4d43a2f81e9f61c426b3cc558',
 'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
 'complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
 'complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def verify(root):
 root=Path(root);blobs={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'Pinned predecessor '+name);blobs[name]=b
 mod=types.ModuleType('_authenticated_affine_primitives');mod.__file__=str(root/'complete86_affine_port_scout.py')
 exec(compile(blobs['complete86_affine_port_scout.py'],mod.__file__,'exec'),mod.__dict__)
 old=json.loads(blobs['complete86_affine_port_scout.json']);parent=json.loads(blobs['complete86_factored_first_root.json'])['forms'][0]
 need(parent['normalized']is True and parent['ledger']['operations']==86,'Actual normalized86 source')
 need(old['source_sha256']==PINS['complete86_affine_port_scout.py'],'Frozen depth-one lineage')
 g=mod.Graph();env=g.literal(parent['source']);baseline=g.emit(env['polynomial'])
 need((baseline['M'],baseline['A'])==(48,38),'Same canonical baseline')
 need(set(baseline['free_ports'])==set(parent['witnesses']+parent['ledger']['fixed_numerals']+['x']),'All supplied witness, ordinary and numeral ports')
 seeds=list(mod.seed_graphs(g,env));need(len(seeds)==6,'All six root charts')
 first={out:dict(seed=name,moves=[])for name,out,_ in seeds};proofs=set();raw_first=0
 def proof(kind,a,b,cuts):
  key=(a,b,tuple(sorted(set(cuts))))
  if key not in proofs:g.proof(a,b,cuts);proofs.add(key)
  return dict(kind=kind,old_node=a,replacement_node=b,cut_nodes=sorted(set(cuts)))
 for name,out,_ in seeds:
  for kind,a,b,cuts in list(mod.moves(g,out)):
   cert=proof(kind,a,b,cuts);raw_first+=1
   changed=g.substitute(out,{a:b});first.setdefault(changed,dict(seed=name,moves=[cert]))
 need(len(first)==old['distinct_complete_sources_across_seeds']==874 and raw_first==old['raw_generated_moves']==1300,'Entire saved first layer recovered')
 first_hashes=sorted(mod.digest(g.emit(out))for out in first)
 need(len(set(first_hashes))==874,'First-layer complete source uniqueness')
 counts=Counter();ledgers=Counter();seen=set();hashes=[];best_hashes=[];by_ledger={};frontier=[];records=[]
 rng=random.Random(660086);assignments=[{n:rng.randrange(-2,4)for n in baseline['free_ports']},{n:Fraction(rng.randrange(-2,4),3)for n in baseline['free_ports']}]
 expected=[mod.eval_source(baseline,a)for a in assignments]
 def record(out,route):
  if out in seen:return
  seen.add(out);p=g.emit(out);mod.validate_source(p)
  need(p['free_ports']==baseline['free_ports'],'Complete interface preserved')
  for a,y in zip(assignments,expected):need(mod.eval_source(p,a)==y,'Complete signed/rational output supplement')
  h=mod.digest(p);hashes.append(h);counts[p['operations']]+=1;ledgers[p['M'],p['A']]+=1
  key=(p['M'],p['A'])
  if key not in by_ledger:by_ledger[key]=dict(packet=p,route=route,source_sha256=h)
  if p['operations']==86:best_hashes.append(h)
  records.append([h,p['M'],p['A']])
 for out,route in first.items():record(out,route)
 raw_second=0;second_identities=set();layer_counts=[]
 for base in sorted(first):
  start=len(seen)
  for kind,a,b,cuts in list(mod.moves(g,base)):
   raw_second+=1;second_identities.add((a,b,tuple(sorted(set(cuts)))));cert=proof(kind,a,b,cuts)
   changed=g.substitute(base,{a:b});route=dict(seed=first[base]['seed'],moves=first[base]['moves']+[cert])
   record(changed,route)
  layer_counts.append(len(seen)-start)
 need(len(set(hashes))==len(seen),'Every retained graph has a distinct complete emitted source')
 minimum=min(counts)
 for (M,A),entry in sorted(by_ledger.items()):
  if not any(m<=M and a<=A and(m<M or a<A)for m,a in by_ledger):frontier.append(entry)
 # Replay descriptors accompany every representative complete source.
 representatives=[]
 for key,entry in sorted(by_ledger.items()):
  representative=dict(entry)
  representative['route']=dict(entry['route'])
  representative['route']['moves']=[dict(cert,old_expression=list(g.nodes[cert['old_node']]),replacement_expression=list(g.nodes[cert['replacement_node']]))for cert in entry['route']['moves']]
  representatives.append(representative)
 return dict(status='PASS_COMPLETE86_TWO_MOVE_CENSUS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),pins=PINS,
  parent=dict(operations=86,M=48,A=38,witnesses=19,exact_degree=179,ordinary_input='x'),
  grammar=dict(seed_names=[name for name,_,_ in seeds],maximum_local_moves=2,primitives_source_sha256=PINS['complete86_affine_port_scout.py'],historical_verify_called=False,new_coordinates=False),
  counts=dict(seed_cut_proofs=12,first_layer_complete_sources=len(first),first_move_instances=raw_first,second_move_instances=raw_second,distinct_second_cut_proofs=len(second_identities),distinct_all_local_cut_proofs=len(proofs),distinct_complete_sources=len(seen),literal_gates_checked=sum((M+A)*n for(M,A),n in ledgers.items()),full_numeric_checks=2*len(seen),signed_checks=len(seen),rational_checks=len(seen)),
  minimum=minimum,minimum_sources=counts[minimum],cost_histogram={str(k):v for k,v in sorted(counts.items())},ledger_histogram=[dict(M=M,A=A,sources=n)for(M,A),n in sorted(ledgers.items())],
  first_layer_source_set_sha256=digest(first_hashes),complete_source_set_sha256=digest(sorted(hashes)),ordered_census_sha256=digest(records),per_first_source_new_counts_sha256=digest(layer_counts),
  minimum_source_hashes=sorted(best_hashes),multiplication_addition_frontier=frontier,representatives_by_ledger=representatives,
  scope='All zero/one/two local moves after exactly six pinned joint-root schedules; complete identical polynomial and unchanged19 positive witnesses. No repeated closure beyond depth2, global circuit lower bound, coordinate weakening or new universal operation bound.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 need(exact(r,json.loads(json.dumps(r))),'Exact typed JSON round trip before writing')
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Exact typed full receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts']);print('minimum',r['minimum'],'histogram',r['cost_histogram']);print('frontier',[(f['packet']['M'],f['packet']['A'])for f in r['multiplication_addition_frontier']])
if __name__=='__main__':main()
