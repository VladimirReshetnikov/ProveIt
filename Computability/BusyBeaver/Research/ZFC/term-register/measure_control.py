"""Bounded source cost and literal blank-prefix measurements, no optimization."""
from pathlib import Path
import argparse,sys,json,time,hashlib
from collections import Counter
from term_register import load_backend
from full_program import FullProgram

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--frontend',type=Path,required=True);ap.add_argument('--compiled',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if not __debug__:ap.error('assertions enabled required')
 sys.setrecursionlimit(30000);sys.path[:0]=[str(a.frontend),str(a.frontend/'source50/code')]
 import term_patterns as V
 start=time.monotonic();templates=V.load_templates(a.frontend/'source50/data/spec254.json');P=FullProgram(load_backend(a.repo,a.output.parent/'backend'),templates);search=P.search()
 parts={'search':search,'verify':P.b.add_sequence(P.verify()),'full_syntax':P.b.add_sequence(P.syntax()),
 'ReadNode':P.read_node(),'row_parser':P.b.add_sequence(P.parse_row()),'proof_lookup_minor':P.b.add_sequence(P.get_formula('premise0','minor')),
 'semantic_rows':P.b.add_sequence(P.semantic_row()),'gate0':P.b.add_sequence(P.gate('arg0','path0')),'gate1':P.b.add_sequence(P.gate('arg1','path1'))}
 for tag,p in templates.items():parts['pattern'+str(tag)]=P.b.add_sequence(P.matcher(p))
 P.b.reduce_to_cons()
 def closure(root):
  pending=[root];result=set()
  while pending:
   i=pending.pop()
   if not isinstance(i,int) or i in result:continue
   result.add(i);pending.extend(P.b.sequences[i].seq)
  return result
 sets={n:closure(i) for n,i in parts.items()};read=sets['ReadNode'];patterns=set().union(*(sets['pattern'+str(t)] for t in templates));gates=sets['gate0']|sets['gate1']
 def counts(pattern):
  out={'visits':0,'constructors':0,'sum_path_lengths':0,'maximum_path_length':0,'potential_ReadNode_calls':0}
  def visit(slot,depth):
   out['visits']+=1;out['sum_path_lengths']+=depth;out['maximum_path_length']=max(out['maximum_path_length'],depth)
   if slot>pattern.arity:
    out['constructors']+=1;_,l,r=pattern.steps[slot-pattern.arity-1];visit(l,depth+1);visit(r,depth+1)
  visit(pattern.root,0);out['potential_ReadNode_calls']=out['sum_path_lengths']+out['constructors'];out['shared_circuit_wires']=len(pattern.steps);return out
 primitive_names=Counter()
 for i in sets['search']:
  for e in P.b.sequences[i].seq:
   if isinstance(e,str) and e.startswith('3.'):primitive_names[e.split('.')[1]]+=1
 # Independently run the emitted complete canonical table on literal blank.
 sys.path.insert(0,str(a.repo/'Computability/BusyBeaver/Research/ZFC'));import audit_tm
 raw=(a.compiled/'full-search.tm').read_bytes();machine=audit_tm.parse_table(raw.decode());labels=json.loads((a.compiled/'state-names.json').read_text());entry=labels.index('main().0')
 q=machine.start;head=0;ones=set();firstentry=None;steps=0;limit=1_000_000
 while steps<limit and q!=machine.halt:
  edge=machine.rows[q,int(head in ones)]
  if edge.write:ones.add(head)
  else:ones.discard(head)
  head+=edge.move;q=edge.target;steps+=1
  if q==entry and firstentry is None:firstentry={'steps':steps,'head':head,'ones_count':len(ones),'ones_sha256':hashlib.sha256(json.dumps(sorted(ones),separators=(',',':')).encode()).hexdigest()}
 assert q!=machine.halt and firstentry is not None
 result={'status':'PASS','scope':'Exact reachable source DAG set counts and a finite literal1M binary prefix; not compiler simulation proof, optimality/lowerbound or consistency evidence.',
 'source_DAG_closure_counts':{n:len(s) for n,s in sets.items()},'shared_helper_accounting':{'ReadNode_body_distinct_DAG_nodes':len(read),'pattern_union_nodes':len(patterns),'pattern_nodes_outside_ReadNode_body':len(patterns-read),'gate_union_nodes':len(gates),'gate_nodes_outside_ReadNode_body':len(gates-read),'verify_outside_patterns_and_ReadNode':len(sets['verify']-patterns-read),'search_outside_verify':len(sets['search']-sets['verify'])},
 'pattern_static_cost':{str(t):counts(p) for t,p in templates.items()},'used_primitive_register_names':sorted(primitive_names),'declared_registers':len(P.names),
 'literal_blank_prefix':{'steps':steps,'halted':False,'state':q,'named_state':labels[q],'head':head,'ones_count':len(ones),'first_full_main_entry':firstentry,'ones_sha256':hashlib.sha256(json.dumps(sorted(ones),separators=(',',':')).encode()).hexdigest()},
 'table_sha256':hashlib.sha256(raw).hexdigest(),'elapsed_seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
