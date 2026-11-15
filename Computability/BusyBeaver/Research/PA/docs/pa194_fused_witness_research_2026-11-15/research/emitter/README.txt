SEPARATE FREE-TERM EMITTER CHECK

verify_fusion.py was written independently of the PA194FW construction
and source checker. It evaluates the complete source macro atom word in
a free term algebra with symbolic independent register inputs. It checks
the exact fused formula, all other saved heads, the explicit binder, and
the exact unguarded gate input. It is a symbolic identity, not selected
numerical examples. Primitive atom implementation and gate execution are
separate obligations discharged by the primary source/physical package.

From the archive root:
  python3 research/emitter/verify_fusion.py \
    primary/machines/PA194FW/grammar.tree.json --output replay/emitter.json

The containing replay directory must exist; verify_release.py creates it.
FW_independent_emitter.json is the recorded original result.
