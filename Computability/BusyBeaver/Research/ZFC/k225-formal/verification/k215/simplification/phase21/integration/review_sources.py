#!/usr/bin/env python3
"""Read-only peer of the final phase21 source repairs and ax_eval relocation."""
import argparse,hashlib,json
from pathlib import Path
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def pin(p):return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def one(text,old,new):
 assert text.count(old)==1,old
 return text.replace(old,new)
def header(text,kind,name):
 start=text.index(kind+' '+name+' ');return text[start:text.index(':=',start)].strip()
def main():
 p=argparse.ArgumentParser()
 for n in ['spec','plan','result','actual-readback','failures','literal-review','output']:p.add_argument('--'+n,type=Path,required=True)
 a=p.parse_args();assert not a.output.exists()
 spec=read(a.spec);q=read(a.plan);actual=read(a.actual_readback);result=read(a.result)
 assert actual['status']=='PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK' and result['status']=='PASS'
 assert actual['result']['sha256']==sha(a.result) and actual['plan']['sha256']==sha(a.plan)==result['map_sha256']
 assert actual['providers']==226 and actual['fresh']==18 and actual['fresh_provider_warnings']==0
 rows={r['module']:r for r in spec['sources']};assert len(rows)==3
 data={};sources=[]
 for m,r in rows.items():
  assert sha(r['before']['path'])==r['before']['sha256']
  assert sha(r['candidate']['path'])==r['candidate']['sha256']==sha(r['canonical'])
  match=next(x for x in q['source_overlay'] if x['module']==m);assert match==r
  data[m]=(Path(r['before']['path']).read_text(),Path(r['candidate']['path']).read_text())
  sources.extend(pin(r[k]['path']) for k in ['before','candidate'])
  sources.append(pin(r['canonical']))
 initial=Path('/tmp/k215-phase21-ax-expr/candidate')
 initial_ax=(initial/'AXWord.lean').read_text();final_ax=data['BusyBeaver.ZFC.AXWord'][1]
 assert initial_ax.count('  | prefix a rest ih')==2
 assert final_ax==initial_ax.replace('  | prefix a rest ih','  | «prefix» a rest ih')
 old_root,new_root=data['BusyBeaver.ZFC.L2Root254'];old_native,new_native=data['BusyBeaver.ZFC.L2Axioms254']
 start=old_root.index('\ntheorem ax_eval ');stop=old_root.index('\n/-! ## The dispatch',start)
 expected_root=old_root[:start]+old_root[stop:]
 expected_root=one(expected_root,'import BusyBeaver.ZFC.Enum254\nimport BusyBeaver.ZFC.L2AxiomsEval254','import BusyBeaver.ZFC.L2Axioms254')
 expected_root=one(expected_root,'`ax_eval` evaluates the generated `axioms()` composite symbolically: the','`ax_eval` evaluates the checked `axioms()` expression symbolically: the')
 expected_root=one(expected_root,'simp [toAS, Enum254.fetch, h, hv]','simp [toAS, Enum254.fetch, hv]')
 assert new_root==expected_root and 'theorem ax_eval ' not in new_root
 old_header=header(old_root,'theorem','ax_eval');assert header(new_native,'theorem','ax_eval')==old_header
 literal=read(a.literal_review)
 assert literal['status']=='PASS_INDEPENDENT_SOURCE_ONLY_LITERAL_SHAPE' and literal['physical_node_shape_checked']
 assert literal['expression_constructors']==247 and literal['semantic_macros_before_final_gate']==180
 assert literal['candidate']['sha256']=='25e48307ed165cd6a920a0e104101f9b1197c06d3f40ecf32eedc32b156ef477'==hashlib.sha256(new_native.encode()).hexdigest()
 for name in ['reader','candidate','DAG_source','shared_checker_source']:assert sha(literal[name]['path'])==literal[name]['sha256']
 initial_native=(initial/'L2Axioms254.lean').read_text()
 native_head=initial_native[:initial_native.index('private abbrev atomAt')]
 native_head=one(native_head,'import BusyBeaver.ZFC.AXWord\n','import BusyBeaver.ZFC.AXWord\nimport BusyBeaver.ZFC.Enum254\n')
 native_head=one(native_head,'A bounded decoder proposes the expression; `axExpr_checked` binds its complete shape\nand effects to the literal program. The shared structural proof supplies its run.','The literal expression names only semantic macros; `axExpr_checked` binds its\ncomplete shape to the program. The shared structural proof supplies its run.')
 literal_decl=new_native[new_native.index('def axExpr : AXExpr :='):new_native.index('theorem axExpr_checked')]
 contracts=initial_native[initial_native.index('theorem axExpr_checked'):initial_native.index('\nend SetTheory.BusyBeaver.ZFC.L2')]
 expected_native=native_head+literal_decl+contracts+'\nset_option maxHeartbeats 1000000 in\n/-- The native AX effect is the enumerator AX step. -/\n'+old_header+' := by\n  simp only [f1, axExpr, axExprEval, AXAtom.effect, pushA, popA, gateF, ofNat_P,\n    Enum254.gate, Enum254.axStack, bundle, bundleC, bundleG, rho1, rho2, rho3, rho4, rho5,\n    rho6, rho7, rho8, Nat.zero_add]\n\nend SetTheory.BusyBeaver.ZFC.L2\n'
 assert new_native==expected_native
 api=[]
 for kind,name in [('def','f1'),('theorem','l1'),('theorem','c1')]:
  h=header(old_native,kind,name);assert h==header(new_native,kind,name)
  api.append({'name':'SetTheory.BusyBeaver.ZFC.L2.'+name,'header_sha256':hashlib.sha256(h.encode()).hexdigest()})
 api.append({'name':'SetTheory.BusyBeaver.ZFC.L2.ax_eval','header_sha256':hashlib.sha256(old_header.encode()).hexdigest(),'moved_from':'L2Root254.lean','moved_to':'L2Axioms254.lean'})
 failures=read(a.failures);assert failures['status']=='PASS_TERMINAL_FAILURE_CONTEXTS_PRESERVED' and len(failures['contexts'])==11 and failures['provider_timeouts']==[6]
 report={'status':'PASS_FINAL_SOURCE_REPAIR_AND_RELOCATION_PEER','reader':pin(__file__),'spec':pin(a.spec),'plan':pin(a.plan),'result':pin(a.result),'actual_readback':pin(a.actual_readback),'failure_readback':pin(a.failures),'literal_review':pin(a.literal_review),'sources':sources,'retained_exact_headers':api,'AXWord_only_two_case_identifier_escapes_since_initial_peer':True,'native_reconstructed_from_checked_literal_exact_contract_block_and_relocated_ax_eval':True,'native_ax_eval_maxHeartbeats':1000000,'Root_remaining_bytes_identical_after_four_explicit_changes':True,'warning_policy_and_compiler_resource_limits_unchanged':True,'scope':'The final source-spec candidates equal their adopted canonical bytes and the accepted actual plan. Relocated ax_eval keeps its exact seven-Nat statement in the same namespace. Its 247-constructor literal follows the same physical DAG, including the fused read and final gate; checked/run/clean declarations are byte-identical to the initial peer. Its effect/Enum proof uses direct symbolic simp. Its local heartbeat bound is explicitly raised from the default 200000 to 1000000; the supervisory 120s/12GiB bounds remain unchanged. All unrelated Root bytes are identical, including the removal of the previously observed unused h argument. Eleven failed contexts, including the genuine v6 timeout, remain separately preserved. No compiler or supplied code was executed by this peer.'}
 with a.output.open('x') as f:json.dump(report,f,indent=2);f.write('\n')
 print(json.dumps({'status':report['status'],'report':pin(a.output)},indent=2))
if __name__=='__main__':main()
