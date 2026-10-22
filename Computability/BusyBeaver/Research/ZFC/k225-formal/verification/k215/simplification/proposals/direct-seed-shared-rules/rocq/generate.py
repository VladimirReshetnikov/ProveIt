#!/usr/bin/env python3
"""Generate a reviewable common proof core and exact-name adapters.

The proof terms are inherited from Jeff's L1_LProp and ProveIt's L224Prop.
This transformation is untrusted; coqc checks all resulting terms and API tests.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
src = (ROOT / 'upstream/ZF/L1_LProp.v').read_text()
body = src[src.index('Lemma llp5'):]
assert len(re.findall(r'^Lemma ', body, re.M)) == 71
assert body.count('(Weq 0 0)') == 12
# These three auxiliary instances use an arbitrary existing formula.  The w0
# already in each theorem's context suffices; no inhabited-carrier premise.
body = body.replace('(Weq 0 0)', 'w0')
for old, new in [('wff','Formula'), ('lprov','Pr'), ('Wim','Imp'),
                 ('Wn','Neg'), ('LDET','mp'), ('LB1','b1'),
                 ('LB2','b2'), ('LB3','b3')]:
    body = re.sub(r'\b' + old + r'\b', new, body)
header = '''(** One propositional proof core for the two K215 named calculi.
    Derived from Jeff's L1_LProp.v; no syntax or equality assumptions.
    See NOTICE.md and evidence/source_manifest.json for source identities. *)
Module Type PropositionalBasis.
  Parameter Formula : Type.
  Parameter Imp : Formula -> Formula -> Formula.
  Parameter Neg : Formula -> Formula.
  Parameter Pr : Formula -> Prop.
  Parameter mp : forall a b, Pr (Imp a b) -> Pr a -> Pr b.
  Parameter b1 : forall a b c,
    Pr (Imp (Imp a b) (Imp (Imp b c) (Imp a c))).
  Parameter b2 : forall a, Pr (Imp (Imp (Neg a) a) a).
  Parameter b3 : forall a b, Pr (Imp a (Imp (Neg a) b)).
End PropositionalBasis.

Module PropositionalRules (B : PropositionalBasis).
Import B.
'''
(ROOT / 'proof/PropositionalCore.v').write_text(header + body + '\nEnd PropositionalRules.\n')

def basis(name, pred, prefix):
    return f'''Module {name} <: PropositionalBasis.
  Definition Formula := wff.
  Definition Imp := Wim.
  Definition Neg := Wn.
  Definition Pr := {pred}.
  Definition mp := {prefix}DET.
  Definition b1 := {prefix}B1.
  Definition b2 := {prefix}B2.
  Definition b3 := {prefix}B3.
End {name}.
'''

names = re.findall(r'^Lemma (\w+)', body, re.M)
standard = '''(** Compatibility facade for ZF.L1_LProp. *)
From ZF Require Import Logic L1_LDef.
From K215Common Require Import PropositionalCore.
''' + basis('StandardBasis', 'lprov', 'L')
standard += 'Include PropositionalRules StandardBasis.\n'
(ROOT / 'proof/L1_LProp.v').write_text(standard)

restricted = '''(** Compatibility facade for K215F.L224Prop; original names retained. *)
From ZF Require Import Logic.
From K215F Require Import L224Def.
From K215Common Require Import PropositionalCore.
''' + basis('RestrictedBasis', 'lprov224', 'M')
restricted += 'Module RestrictedRules := PropositionalRules RestrictedBasis.\n'
restricted += '\n'.join(f'Definition m{n} := RestrictedRules.{n}.' for n in names) + '\n'
(ROOT / 'proof/L224Prop.v').write_text(restricted)

checks = '''(** The full old API is restated verbatim; all names must still typecheck. *)
From ZF Require Import Logic L1_LDef L1_LProp.
From ZF Require Import L1_LMeta.
From K215F Require Import L224Def L224Prop L224Meta.
'''
for lane, path in [('standard','upstream/ZF/L1_LProp.v'),
                   ('restricted','upstream/K215F/L224Prop.v')]:
    original = (ROOT / path).read_text()
    for name, params, statement in re.findall(r'^Lemma (\w+) (\([^\n]+\)) : ([^\n]+)\.$', original, re.M):
        checks += f'Example {lane}_{name} {params} : {statement}.\n'
        checks += f'Proof. exact ({name} ' + ' '.join(re.findall(r'\((.*?) :', params)[0].split()) + '). Qed.\n'
for n in names:
    if n.startswith('lpc_'):
        checks += f'Print Assumptions standard_{n}.\n'
        checks += f'Print Assumptions restricted_m{n}.\n'
checks += '''Print Assumptions L1_LMeta.ae_sound.
Print Assumptions L224Meta.malpha.
'''
(ROOT / 'proof/PropositionalAPIAudit.v').write_text(checks)
