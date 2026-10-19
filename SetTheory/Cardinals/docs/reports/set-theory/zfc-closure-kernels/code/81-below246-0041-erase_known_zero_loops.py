#!/usr/bin/env python3
"""Build and audit the occurrence-level erasure of two known-zero transfers.

Inputs: Mira-Cult's literal 254-program tree, verified by Jeff Ketchersid.
The two unreachable positive guards were identified by ProveIt. The present
contribution strengthens their invariant to arbitrary initial root registers
and checks exact control correspondence after the two tree contractions.
This is a register-program artifact, not a binary machine or new state bound.
"""
from pathlib import Path
import hashlib
import json
import re
import audit_phase as a

OUT = Path(__file__).resolve().parent

def parse_nodes(raw):
    s=raw.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    token=r'(?:CN|CI|CD|CB|CC) \d+|CH'
    return [tuple(tuple(x.split()) for x in m) for m in
            re.findall(r'\(('+token+r'),\s*('+token+r')\)',s)]

def main():
    raw=a.PROGRAM.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==a.EXPECTED
    leaves,cases,by_leaf,first=a.read_program(raw)
    phase=a.analyze(leaves,cases,by_leaf,first,[7]*9)
    assert phase['impossible_cases']==[8202,8203,8204,8358,8359,8360]
    masks=[None if i is None else tuple(phase['mask_classes'][i])
           for i in phase['site_mask_class_ids']]
    nodes=parse_nodes(raw)
    old_lookup={l[0]:i for i,l in enumerate(leaves)}
    new_leaves=[]; new_nodes=[]; mapping={}; root_edge=None

    def edge(e,old_path,new_path):
        op=e[0]; n=int(e[1]) if len(e)>1 else None
        if op=='CN': return visit(n,old_path,new_path)
        old_i=old_lookup[old_path]
        mapping[old_i]=len(new_leaves)
        new_leaves.append((new_path,op,n,old_i))
        return (op,n)

    def visit(old_node,old_path,new_path):
        if old_node in (6323,6435):
            return edge(nodes[old_node][1],old_path+'1',new_path)
        new_i=len(new_nodes); new_nodes.append(None)
        children=tuple(edge(e,old_path+str(b),new_path+str(b))
                       for b,e in enumerate(nodes[old_node]))
        new_nodes[new_i]=children
        return ('CN',new_i)

    root_edge=visit(0,'','')
    assert root_edge==('CN',0)
    assert len(new_leaves)==6454 and len(new_nodes)==6453
    lookup={p:i for i,(p,_,_,_) in enumerate(new_leaves)}

    def decode(pc):
        q=0; p=''; depth=0
        for _ in range(len(new_nodes)+1):
            b=pc[depth] if depth<len(pc) else '0'; p+=b; depth+=1
            op,n=new_nodes[q][int(b)]
            if op=='CN': q=n
            else:
                assert '1' not in pc[depth:]
                return lookup[p]
        raise AssertionError('invalid transformed tree')

    zero_bypass={cases[c][0]:cases[c][2] for c in (8201,8357)}
    assert all(masks[i][leaves[i][2]]==1 for i in zero_bypass)
    correspondence=[]; max_omitted=0
    for c,(old_i,positive,old_j) in enumerate(cases):
        if old_i not in mapping: continue
        assert c not in phase['impossible_cases']
        omitted=0
        while old_j in zero_bypass:
            omitted+=1; old_j=zero_bypass[old_j]
        max_omitted=max(max_omitted,omitted)
        assert old_j is None or old_j in mapping
        expected=None if old_j is None else mapping[old_j]
        new_i=mapping[old_i]; p,op,n,_=new_leaves[new_i]
        pc=a.next_pc(p,op,n,positive)
        actual=None if pc is None else decode(pc)
        assert actual==expected, (c,expected,actual)
        # The contraction must also preserve the arbitrary-root invariant.
        out=a.transfer(masks[old_i],leaves[old_i],positive)
        assert out is not None
        if old_j is not None:
            assert all(x&~y==0 for x,y in zip(out,masks[old_j]))
        correspondence.append([c,new_i,positive,actual,omitted])
    assert len(correspondence)==8383 and max_omitted==1
    assert decode('')==mapping[first]

    def fmt(e): return e[0] if e[1] is None else f'{e[0]} {e[1]}'
    intro='''(** Two known-zero transfer occurrences erased from Mira-Cult's
    register program (Jeff Ketchersid verification source, ProveIt intake).

    This generated tree is an experimental compiler input. Its ordinary
    root-halting equivalence is established by the accompanying phase and
    control correspondence certificates. No Coq proof of that equivalence
    and no new binary-state bound is asserted by this file.

    Original tree SHA-256:
    1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746
    Occurrence rewrites: CN6323 -> CI5; CN6435 -> CN6438.
    Existing break/continue counts are retained after verified rebasing. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith NArith.
From M254 Require Import RM RMEquiv.
Import ListNotations.

Inductive phase_edge : Type :=
  CN (m : N) | CI (r : nat) | CD (r : nat) | CB (k : nat) |
  CC (k : nat) | CH.
Arguments CN m%N_scope.

Definition phase_cv (e : phase_edge) : edge :=
  match e with
  | CN m => ENode (N.to_nat m)
  | CI r => EInc r
  | CD r => EDecnz r
  | CB k => EBreak k
  | CC k => EContinue k
  | CH => EHalt
  end.

Definition phase_tab : list (phase_edge * phase_edge) := [
'''
    body=';\n'.join(f'  ({fmt(left)}, {fmt(right)})' for left,right in new_nodes)
    coq=intro+body+'''\n].

Definition phase_prog : prog := {|
  nodes := fun n => let '(a, b) := nth n phase_tab (CH, CH)
                   in (phase_cv a, phase_cv b);
  root := 0;
  nnodes := 6453
|}.
'''
    (OUT/'ProgPhaseErased.v').write_text(coq)
    graph={'source_program_sha256':a.EXPECTED,
           'nodes':[[list(x),list(y)] for x,y in new_nodes],
           'leaves':[{'path':p,'op':op,'arg':n,'old_leaf':i} for p,op,n,i in new_leaves]}
    (OUT/'program_phase_erased.json').write_text(json.dumps(graph,separators=(',',':'))+'\n')
    proof={'source_program_sha256':a.EXPECTED,
           'new_tree_sha256':hashlib.sha256(coq.encode()).hexdigest(),
           'ordinary_theorem':'Root halting is unchanged for every nine-register input.',
           'phase':phase,
           'deleted_old_leaves':[i for i in range(len(leaves)) if i not in mapping],
           'old_to_new_leaf_map':mapping,
           'guard_correspondence':correspondence,
           'max_identity_steps_omitted_between_retained_steps':max_omitted,
           'unchanged_break_continue_counts':True,
           'all_retained_successors_compared':True,
           'new_literal_nodes':len(new_nodes),'new_instruction_leaves':len(new_leaves),
           'new_guard_count':len(correspondence),
           'scope':'Ordinary invariant and program equivalence; no binary compiler theorem.'}
    (OUT/'phase_erasure_certificate.json').write_text(json.dumps(proof,separators=(',',':'))+'\n')
    print(json.dumps({k:proof[k] for k in ['new_tree_sha256','deleted_old_leaves','new_literal_nodes',
          'new_instruction_leaves','new_guard_count','max_identity_steps_omitted_between_retained_steps',
          'all_retained_successors_compared']},indent=2))

if __name__=='__main__': main()
