# Instantiating the uniqueness matrix

`uniq_outer_instance` and `uniq_inner_instance` compute two successive substitutions of model-valued free-variable indices through the two binders in the PAeq uniqueness formula for an arbitrary internally valid arity-zero term. The first substitution retains the inner binder and uses Foundation's q-vector substitution and bound-shift laws; the second produces the explicit disjunction of three equality atoms. The two indices and the valid term may be nonstandard. The modules also prove the necessary formula validity and generic equality-atom substitution lemma.

Replay from the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-name-uniq-subst.sh "$PWD" /dev/shm/pa194-name-uniq-subst-repo-NEW-new
```

The checker recompiles both sources against `/dev/shm/pa194-guarded-all-left-repo-v2`, `/dev/shm/pa194-name-unique-repo`, and the retained objects listed in the script, including prebuilt Foundation. It requires five clean axiom reports and rejects `sorryAx`. These are syntax identities in IΣ₁ arithmetic models; they do not prove `nameOfUniq`, construct a full interpretation, or give a native iPRA theorem.
