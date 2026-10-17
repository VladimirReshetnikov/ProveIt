"""Price a source-level MP-success stack-interface simplification.

The fixed full base4 calculus/generator stays unchanged. Only source DAG130's
successful equality continuation skips par1's initial pushwff, using its existing
copy/restore tail instead. The associated proof compiler needs one fewer final
NIP in the MP block. This is an unproved changed-interface experiment, not a
mutation of the checked252 table or a new consistency bound.
"""
from pathlib import Path
import argparse,hashlib,importlib,json,sys,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
 R=a.repo.resolve();W=a.output.resolve();assert not W.is_relative_to(R)and(not W.exists()or not any(W.iterdir()))
 W.mkdir(parents=True,exist_ok=True);research=R/'Computability/BusyBeaver/Research/ZFC';sys.path.insert(0,str(research))
 import recover_wade_dag as C
 import mira_backend as M
 from audit_tm import parse_table
 source=C.git_bytes(None,'ZF/m254/coq/prog/Dag254.v');nodes,names=C.parse_dag(source.decode());assert len(nodes)==219
 changed=dict(nodes);assert nodes[130]==('ENode 123','ENode 166') and nodes[166]==('ENode 171','ENode 167') and nodes[167]==('ENode 198','ENode 205')
 changed[130]=('ENode 123','ENode 167');assert [(q,nodes[q],changed[q])for q in nodes if nodes[q]!=changed[q]]==[(130,('ENode 123','ENode 166'),('ENode 123','ENode 167'))]
 backend_dir=W/'wade';backend_dir.mkdir()
 for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):(backend_dir/name).write_bytes(C.git_bytes(None,'ZF/generator/'+name))
 sys.path.insert(0,str(backend_dir));B=importlib.import_module('TMBuilder')
 def canon(tm,path):
  states={q for q,_ in tm.states};order=[tm.start]+sorted(states-{tm.start});labels={q:i for i,q in enumerate(order)};halt=len(order);rows=[];missing=[]
  for q in order:
   for bit in ('0','1'):
    if(q,bit)in tm.states:
     act=tm.states[q,bit];w,move,target=act.write,act.direction,act.nextstate
     assert target in states or target=='halt';target=labels.get(target,halt)
    else:w,move,target=bit,'R',halt;missing.append([q,int(bit)])
    assert w in ('0','1')and move in ('L','R');rows.append(f'{labels[q]} {bit} {w} {move} {target}')
  path.write_text('#! start 0\n'+'\n'.join(rows)+'\n');back=parse_table(path.read_text());assert len(back.rows)==2*len(states)and len(back.states)==len(states)and back.start==0 and back.halt==halt
  return dict(working_states=len(states),rows=len(rows),missing_source_rows=missing,totalized_missing_row_action='preserve readbit, moveR, halt; preserves undefined-row halting/tape with final extra move',sha256=sha(path),path=str(path))
 def boot(tm):
  q=tm.start;head=0;tape=set();n=0
  while q!=names[0]:
   bit='1'if head in tape else'0';act=tm.states[q,bit]
   if act.write=='1':tape.add(head)
   else:tape.discard(head)
   head+=1 if act.direction=='R'else-1;q=act.nextstate;n+=1
   assert n<=1000000,'bounded bootstrap control did not reach root'
  return dict(steps=n,state=q,head=head,one_cells=sorted(tape),one_count=len(tape),scope='first source-root entry; complete tape equality control, not a new register-frame proof')
 results={};start=time.monotonic()
 for label,ns in [('baseline',nodes),('mp_no_dummy_push',changed)]:
  d=W/label;d.mkdir();(d/'dag.json').write_text(json.dumps({str(q):list(ns[q])for q in sorted(ns)},indent=2)+'\n')
  t=time.monotonic();tm=C.compile_dag(B,ns,names);C.reextract(tm,ns,names);tm.save(str(d/'wade-named.tm'))
  w=canon(tm,d/'wade-total.tm');w['seconds']=time.monotonic()-t;w['root_boot']=boot(tm);w['framework_states']=len({q for q,_ in tm.states if q[0].isdigit()});w['decision_states']=w['working_states']-w['framework_states'];w['reextracted_DAG_exact']=True
  mm=M.compile_dag(ns,names,initializer='compact');mm.check_sites();mm.save(d/'mira-compact.tm');assert sha(d/'mira-compact.tm')==mm.evidence['machine_sha256'];mc=dict(mm.evidence);mc['initial_configuration_check']=M.initial_configuration_check(mm);mc['path']=str(d/'mira-compact.tm')
  sites=M.instruction_sites(ns);results[label]=dict(dag_sha256=sha(d/'dag.json'),dag_nodes=len(ns),instruction_sites=len(sites),wade=w,mira_compact=mc)
 assert results['baseline']['wade']['root_boot']==results['mp_no_dummy_push']['wade']['root_boot']
 assert results['baseline']['mira_compact']['initial_configuration_check']==results['mp_no_dummy_push']['mira_compact']['initial_configuration_check']
 frozen=research/'candidate-permutation252/zfc_permutation252.tm';assert sha(frozen)=='8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797';fm=parse_table(frozen.read_text());assert len(fm.states)==252 and len(fm.rows)==504
 compiler_source=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean';compiler_text=compiler_source.read_text();old_mp=compiler_text[compiler_text.index('def mpBlock '):compiler_text.index('theorem mp_contract ')]
 assert old_mp.count('(nips 10 ++ [.drop 0, .nip 0, .nip 0])')==1
 new_mp=old_mp.replace('def mpBlock ', 'def mpBlockWithoutDummy ').replace('(nips 10 ++ [.drop 0, .nip 0, .nip 0])','(nips 10 ++ [.drop 0, .nip 0])')
 (W/'modified-mp-block.lean').write_text(new_mp+'-- Source-only definition excerpt; no execution theorem is asserted.\n')
 result=dict(status='PASS_NEGATIVE_STATE_COST_CONTROL',elapsed_seconds=time.monotonic()-start,scope=__doc__,upstream_commit=C.COMMIT,source_sha256=hashlib.sha256(source).hexdigest(),baseline_frozen252=dict(path=str(frozen),sha256=sha(frozen),working_states=252,rows=504,mutated=False,regenerated=False),changed_DAG_edge=dict(node=130,before=list(nodes[130]),after=list(changed[130])),results=results,full_calculus_and_theory_rows_unchanged=True,fresh_initializer_charged_in_both_backends=True,modified_compiler_final_NIP_removed_in_source=True,modified_compiler_definition=dict(path=str(W/'modified-mp-block.lean'),sha256=sha(W/'modified-mp-block.lean'),built=False),original_compiler_definition_source=dict(path=str(compiler_source),sha256=sha(compiler_source)),source_level_proof_obligations=['prove changed MP interface from original helper contracts','prove altered compilempBlock contract with one finalNIP removed','prove whole proof-search calibration for altered source','prove any generated binary simulation'],no_smaller_machine_claim=True,source_hashes={str(q):sha(q)for q in [Path(__file__).resolve(),research/'recover_wade_dag.py',research/'mira_backend.py',research/'compact_initializer.py',research/'audit_tm.py' ] if q.is_file()})
 (W/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:dict(sites=v['instruction_sites'],wade=v['wade']['working_states'],mira=v['mira_compact']['working_states'],boot=v['mira_compact']['initializer_steps'])for k,v in results.items()},indent=2));print(W/'results.json')
if __name__=='__main__':main()
