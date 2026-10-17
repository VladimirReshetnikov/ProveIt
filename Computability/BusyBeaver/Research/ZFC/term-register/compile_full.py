"""Compile the complete blank primitive-register certificate search, offline.

The public Wade compiler is pinned/recovered unchanged; no compiler simulation
proof is asserted. All helper bodies, full parser, all12 rules, both gates,
fixedF endpoint, candidate scheduler and original blank bootstrap are charged.
"""
import argparse,hashlib,json,sys,time
from pathlib import Path
from collections import Counter
from term_register import load_backend
from full_program import FullProgram

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--frontend',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if not __debug__:ap.error('assertions must remain enabled')
 sys.setrecursionlimit(30000);a.output.mkdir(parents=True,exist_ok=True)
 sys.path[:0]=[str(a.frontend),str(a.frontend/'source50/code')]
 import term_patterns as V
 templates=V.load_templates(a.frontend/'source50/data/spec254.json');start=time.monotonic()
 P=FullProgram(load_backend(a.repo,a.output/'backend'),templates);root=P.search()
 # ReadNode's standalone testing name must never select the helper as main.
 for s in P.b.sequences:s.name=None
 P.b.sequences[root].name='main().0'
 P.b.reduce_to_cons();assert P.b.find_seq('main().0')==root
 reachable=set(P.b.reachable());assert root in reachable
 P.b.name_sequences();assert P.b.find_seq('main().0')==root
 assert len({P.b.sequences[i].name for i in reachable})==len(reachable)
 P.b.generate();before=len({q for q,b in P.b.tm.states});P.b.tm.gc();states={q for q,b in P.b.tm.states}
 P.b.tm.save(a.output/'full-search-named.tm')
 # Canonical standard binary totalization. Undefined-action source halts;
 # completion writes0/movesR/enters the single explicit terminal. Only halting
 # equivalence is intended, not equal terminal head/tape or step counts.
 ordered=[P.b.tm.start]+sorted(states-{P.b.tm.start});number={q:i for i,q in enumerate(ordered)};halt=len(states)
 rows=['#! start 0'];filled=[];terminals=set()
 for q in ordered:
  for bit in ('0','1'):
   t=P.b.tm.states.get((q,bit))
   if t is None:w,d,target='0','R',halt;filled.append([number[q],int(bit)])
   else:
    w,d=t.write,t.direction;assert w in ('0','1') and d in ('L','R')
    if t.nextstate not in states:terminals.add(t.nextstate)
    target=number.get(t.nextstate,halt)
   rows.append(f'{number[q]} {bit} {w} {d} {target}')
 raw=('\n'.join(rows)+'\n').encode();(a.output/'full-search.tm').write_bytes(raw)
 (a.output/'state-names.json').write_text(json.dumps(ordered,indent=2)+'\n')
 # Independent maintained strict table parser verifies exactly2rows/state,
 # one terminal, no duplicate/source-format mistakes and actual graph count.
 sys.path.insert(0,str(a.repo/'Computability/BusyBeaver/Research/ZFC'))
 import audit_tm
 machine=audit_tm.parse_table(raw.decode());assert len(machine.states)==len(states) and machine.halt==halt
 graph=audit_tm.graph_reachable(machine);assert graph==set(range(halt+1))
 def zero_depth(i):
  e=P.b.sequences[i].seq[0]
  return 1+zero_depth(e) if isinstance(e,int) else 1
 maxdepth=max(zero_depth(i) for i in reachable)
 categories=Counter('framework' if q[0].isdigit() else 'register' if q.startswith('r.') else 'control' for q in states)
 source={str(Path(__file__).parent/n):hashlib.sha256((Path(__file__).parent/n).read_bytes()).hexdigest() for n in ('term_register.py','full_program.py','compile_full.py')}
 record={'status':'compiled_experimental_complete_control','calibration':'No new compiler/codec/scheduler Lean proof. Finite differential tests are separate. This is not a smaller-machine or consistency claim.',
 'working_states':len(states),'halt_state':halt,'total_binary_rows':2*len(states),'table_sha256':hashlib.sha256(raw).hexdigest(),
 'register_count':len(P.names),'register_names':P.names,'charged_source_binary_DAG_nodes':len(reachable),'max_dispatch_zero_depth':maxdepth,
 'states_before_graph_gc':before,'categories':dict(categories),'partial_row_totalizations':filled,'undefined_named_terminals':sorted(terminals),
 'blank_tape':'bi-infinite all0, initialhead0,state0;0/1symbols;write-then-moveL/R before terminal entry',
 'candidate_codec':'nil0;cons(bit,tail)=2tail+bit+1;natural enumeration starting0 visits every finite binaryword',
 'elapsed_seconds':time.monotonic()-start,'source_sha256':source,
 'frontend_spec_sha256':hashlib.sha256((a.frontend/'source50/data/spec254.json').read_bytes()).hexdigest(),
 'compiler_sources_sha256':{n:hashlib.sha256((a.output/'backend'/n).read_bytes()).hexdigest() for n in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade')}}
 (a.output/'compilation.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))

if __name__=='__main__':main()
