#!/usr/bin/env python3
"""Export the two certified source trees as Rocq compiler inputs.

These are definitions, not newly compiled Rocq proofs. The independent Python
source audits establish the finite premises of the mathematical equivalences.
"""
from pathlib import Path
import json
import re

ROOT=Path(__file__).resolve().parent

def export(stem,module,json_name):
    nodes=json.loads((ROOT/'agent_logic'/json_name).read_text())['nodes']
    assert len(nodes)==6459
    def fmt(e):return e[0] if e[1] is None else f'{e[0]} {e[1]}'
    body=';\n'.join('  ('+fmt(a)+', '+fmt(b)+')' for a,b in nodes)
    text=f'''(** Certified source-transformation input for ProveIt / M254.
    Source program: Mira-Cult; upstream verification: Jeff Ketchersid;
    compiler framework: Andrew James Wade. Original attribution is retained
    in the frozen input package. This file contains new transformed syntax.

    No Rocq compilation or kernel proof of its equivalence is asserted here.
    See the independent source certificates and report.tex for the ordinary
    mathematical proof. This is a register program, not a binary TM table.
*)
From Coq Require Import Lists.List Bool.Bool Arith.Arith NArith.
From M254 Require Import RM RMEquiv.
Import ListNotations.

Module {module}.
Inductive cedge : Type := CN (m : N) | CI (r : nat) | CD (r : nat)
  | CB (k : nat) | CC (k : nat) | CH.
Arguments CN m%N_scope.

Definition cv (e : cedge) : edge :=
  match e with
  | CN m => ENode (N.to_nat m) | CI r => EInc r | CD r => EDecnz r
  | CB k => EBreak k | CC k => EContinue k | CH => EHalt
  end.

Definition table : list (cedge * cedge) := [
{body}
].

Definition program : prog := {{|
  nodes := fun n => let '(a,b) := nth n table (CH,CH) in (cv a,cv b);
  root := 0;
  nnodes := 6459
|}}.
End {module}.
'''
    # Check the serialized data, rather than claiming to have run Rocq.
    s=text.split('Definition table',1)[1].split('[',1)[1].split('].',1)[0]
    term=r'(?:CN|CI|CD|CB|CC) \d+|CH'
    regex=r'\(('+term+r'),\s*('+term+r')\)'
    assert not re.sub(r'[;\s]','',re.sub(regex,'',s))
    def parse(t):
        op,*n=t.split();return [op,int(n[0]) if n else None]
    recovered=[[parse(a),parse(b)] for a,b in re.findall(regex,s)]
    assert recovered==nodes
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    (out/(stem+'.v')).write_text(text)
    print(stem,'PASS data roundtrip; Rocq not run')

if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without -O.')
    export('ProgReassociated202','Reassociated202','rotation245_program_tree.json')
    export('ProgZeroSix202','ZeroSix202','rotation_zero_program_tree.json')
