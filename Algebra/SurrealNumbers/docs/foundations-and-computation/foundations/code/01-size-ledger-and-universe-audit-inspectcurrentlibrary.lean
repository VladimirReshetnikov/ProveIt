/-
Inspection script for a checkout of vihdzp/combinatorial-games at
02b4a908ea2ecfefffecb438f691951a814a5264.
Status: NOT RUN in the environment used to prepare the article.
Copy this file into the repository root and run:
  lake env lean InspectCurrentLibrary.lean
after building the imported modules in that pinned checkout.
These commands inspect available declarations; they do not audit every axiom
of every imported theorem, nor do they prove the normal-form bridge.
-/
import CombinatorialGames.Surreal.Division
import CombinatorialGames.Surreal.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.HEval

set_option pp.universes true in
#check Surreal

#synth Field Surreal
#check SurrealHahnSeries
#check SurrealHahnSeries.mk
#check SurrealHahnSeries.small_support
#check HahnSeries.SummableFamily
#check PowerSeries.heval
