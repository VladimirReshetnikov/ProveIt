# Universal compiler rule for one-level quantified bodies

`simRuleAll_oneLevel` proves the universal-introduction compiler field for any `OneLevelQF` source body: arbitrary Boolean structure with quantified descendants having quantifier-free bodies, including mixed equality and membership atoms. Its only hypotheses are source sequent validity, membership of the universal formula, and `OneLevelQF` of the body. No admission or reserve condition is needed. The proof uses an internal Σ₁ structural induction and the separately replayed exact one-binder opening translation. The source model satisfies PRA and IΣ₁, and source codes and Boolean depth may be nonstandard.

The theorem does not cover arbitrary nesting, construct a compiler, identify the source theory with PA, connect to the physical machine, or prove either machine/consistency direction.

The independent incremental replay rebuilt this source and an audit top against separately source-replayed one-binder, quantifier-free-opening and full-one-level baselines. Other workspace dependencies remain prebuilt. Run `check-one-level-free.sh --out OUTPUT` for the repository source-closure audit; see `check_bridge.py` for retained workspace foundations.
