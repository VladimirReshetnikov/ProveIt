#!/usr/bin/env python3
"""Independent source, splice, and Q-head exchange binding for PA194QHS.

Source flattening/resolution and the K/S/MP certificate checker are inherited
from the QH packet; the new whole-source splice checks bind the symmetric
Shift. The general loop proof is in proof/shift_preservation.tex.
"""
from pathlib import Path
import argparse,json,hashlib
from structure_tools import *

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('machine',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 root=Path(__file__).resolve().parent.parent;candidate=a.machine
 grammar=load(root/'construction/inputs/q.grammar.json');oldgrammar=load(root/'construction/inputs/primary.grammar.json')
 newword,oldword=macro_word(grammar),macro_word(oldgrammar)
 require(len(newword)==len(oldword)==190,'word length')
 require(newword[:102]==oldword[:102]and newword[121:]==oldword[121:],'changed AX block')
 U=lambda i,f:('U',i,f)
 P,Q,R=U('D','A'),U('D',imp('A','H')),U('D','H')
 require(execute_block(oldword[102:121])==(['old_T'],raw(imp(P,imp(Q,R)))),'old head')
 require(execute_block(newword[102:121])==(['old_T'],raw(imp(Q,imp(P,R)))),'new head')
 nodes=load(candidate/'nodes.json')
 require(nodes['node163']==['node6','node54'],'visible no-push MP')
 require(nodes['node170']==[['node36',['node167','node145']],'node56'],'symmetric source')
 require(nodes['node171']==['node170',[['leaf','inc',5],['leaf','continueTo',3]]],'new source tail')
 sites=flatten(nodes,grammar);ins=resolve_by_intervals(sites)
 require(sites==load(candidate/'sites.json'),'sites');require(ins==load(candidate/'instructions.json'),'instructions')
 parentnodes=dict(nodes);parentnodes['node170']=[['node36',['node167','node145']],'node57'];parentnodes['node171']=['node170','node23']
 parent=resolve_by_intervals(flatten(parentnodes,grammar))
 require(parent==load(root/'construction/inputs/parent_QH.instructions.json'),'pinned parent source')
 require(len(parent)==3653 and len(ins)==3650 and parent[:3648]==ins[:3648],'outside source binding')
 require(parent[3648:]==[['dec',6,3651,3649],['inc',5,3650],['jump',3648],['inc',6,3652],['jump',0]],'parent restore loop')
 require(ins[3648:]==[['inc',5,3649],['jump',0]],'child tail')
 targets=lambda r:r[2:]if r[0]in('inc','dec')else r[1:]if r[0]=='jump'else[]
 incoming=[[i,t]for i,row in enumerate(parent[:3648])for t in targets(row)if t>=3648]
 require(incoming==[[3644,3648]],'external suffix entries')
 require(parent[3644:3648]==[['dec',5,3648,3645],['inc',1,3646],['inc',6,3647],['jump',3644]],'H-to-TX entry loop')
 guard=[['dec',5,4,1],['dec',6,3,2],['jump',0],['jump',5],['dec',6,10,5],['dec',5,7,6],['jump',5],['dec',6,9,8],['jump',5],['jump',11],['halt']]
 require(ins[:11]==parent[:11]==guard,'exact comparator binding')
 exchange=check_exchange(load(root/'verification/exchange_certificate.json'))
 result=dict(status='PASS',source_sites=3650,unchanged_prefix=3648,old_suffix=parent[3648:],new_suffix=ins[3648:],only_external_suffix_entry=incoming,comparator_program=guard,
  source_resolved_by_independent_interval_method=True,emitter_only_changed_token_interval=[102,121],exchange=exchange,
  new_shift_macro='halt iff h=1; otherwise(h,tail(w),d,head(w))',
  suffix_relation='old(H,X)=(n,1); new(H,X)=(1,n); same T,W and other registers',
  source_step_saving='0 if n=0; 4 if n=1; 2*n+4 if n>=2 (suffix plus common comparator)',
  proof_scope='Exact finite source and proof-certificate bindings. The universally quantified loop and trace proof is mathematical, not a proof-assistant kernel export.',
  dense_sha256=hashlib.sha256((candidate/'machine.tm').read_bytes()).hexdigest())
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
