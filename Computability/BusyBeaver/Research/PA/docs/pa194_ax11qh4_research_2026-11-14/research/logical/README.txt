Logical research supplement — 14 November 2026

RESULT
======
There is a replayed fixed proof-template equivalence between

  G  = (V -> U(c, S -> (P -> 1))) -> 1
  G' = (V -> U(c, P -> (S -> 1))) -> 1.

This is a relative numerical-calculus result. There is no new physical
machine in this supplement and no absolute iPRA/Con(PA) calibration theorem.
Two source-level searches failed to reach a projected total of 194 states.
The main archive's separately validated physical designs are independent
of this source-level research.

PROOF REPLAY
============
From this directory, with Python 3 and assertions enabled:

  python3 check_gate_exchange.py

The script reads an upstream Lean file as proof-term data. It checks
55,585 rows deriving K, S, and exchange from dominated rho8 and MP, then
constructs and audits the outer gate proof with each of the ordinary and
exchanged distribution axioms. It does not invoke Lean. The output under
evidence/ includes the finite outer certificates and machine-readable
receipts. Every rho8 domination fact is justified by subterm inclusion.

SEARCH REPLAY
=============
The search files are self-contained and need a C++17 compiler. From search/:

  c++ -O3 -std=c++17 search.cpp -o search_known
  ./search_known seeds.txt leaf_attrs.txt replay_known 300 14112620

  c++ -O3 -std=c++17 search_qflip.cpp -o search_new
  ./search_new qflip_seeds.txt leaf_attrs.txt replay_new 300 14112621

These are heuristic time-bounded searches. Runs on different hardware need
not execute the same number of moves or reach the same minimum. Original
logs and best grammars are included. Summary:

  Existing inner-S exchange: readers 70 - 7 folds = 63, projected 197.
  New quantified exchange:   readers 73 - 7 folds = 66, projected 200.

The projected totals add the inherited fixed-state term 134. They are not
verified full-machine state counts. A score is not a lower bound. The best
grammars have not been promoted to machine candidates or literal-checked.

The known-exchange run used the inherited seed-pool cutoff <=62. Therefore
its score-63 improvement was saved but not retained as a pool seed. The
new-gate run changed this cutoff to current_best+1. Both search sources
disable head-order and parameter-renaming changes, preserving the selected
190-token word. Compatibility checks for simultaneous folds remain enabled.

PRIOR ART
=========
The exchange inside S and the exchange of its conjunction order already
appear in PA194G exploratory inputs. They are explicitly not claimed as
new here. The new-gate experiment combines its outer quantified exchange
with those four existing inner-S choices and both primary/Q distribution
grammars. No claim of globally new logical equivalence is made.

READING
=======
logical_research.tex is a standalone report with equations, the proof idea,
scope limitations, exact minima, provenance, and further research questions.
The parent archive may include its compiled PDF. PROVENANCE.json records
the pinned repository revision and hashes of included materials.

LICENSE
=======
Imported/adapted repository material is supplied with the original license
at vendor/UPSTREAM_LICENSE. Newly written analysis and checker code are
provided as part of this research package; attribution of the imported
restricted implication proof and search infrastructure remains explicit.
