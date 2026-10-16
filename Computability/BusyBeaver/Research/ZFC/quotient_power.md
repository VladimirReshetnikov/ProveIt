# Power Set in the CP/GIC quotient

`QuotientPower.lean` derives the actual quotient Power Set axiom from
`ProfileModel.ModelsCPGIC` and an explicit raw witness. It uses the checked
formula-indexed Separation adapter and the existing power filter. The
target `quotient_power` ranges over every element of the quotient domain,
and `quotient_pow_form` gives the repository's actual `Pow_form` under
every valuation. It is the first-order Power Set axiom within that model,
not a claim that its power objects contain every external subset.

The trace resource is a literal collection instance. Specialize
`QuotientSeparation.separation_instance` to source formula `Mem(0,1)`
and a constant parameter environment at x. This yields

```text
CollectionInstance mem
  (SeparationChoice mem a (fun z => Member mem z x))
```

for every x. `PowerSyntax.power_instance` supplies the independent
bounded-filter instances. `ProfileAxioms.power_of_instances` combines
these with the existing CP containers, bisimulation equivalence and
interpreted Extensionality. The common bound includes raw traces outside
the initial container, as required by that theorem; no new restriction to
one container or arbitrary semantic collection axiom is introduced.

`interpreted_power` therefore gives p with

```text
Member mem x p ↔ InterpretedSub mem x a
```

for every raw x. `quotient_sub` checks that quantification over all quotient
objects is exactly this interpreted subset relation. Quotient induction
then gives the actual Power Set property for every quotient a and x.
`ZF.Zf.bridge_Pow` connects that property to the literal `Pow_form`.

The trace/filter argument follows upstream `S_ax.v:S_power` at
`297ab8df7e5de329605c3875b4934643b371a5e3`, through the repository's
existing equality-free profile resources. The generic module does not
assume IR, raw Extensionality or profile congruence. Encoded-bundle models
can enter through `Code254GIC` with that adapter's explicit IR and
valuation hypotheses. The other quotient ZF axioms, ordinary Infinity,
the opposite ZFC-to-source interpretation and the machine endpoint remain
separate. No literal table or state count changes.

The 75-line module compiles using the explicit pinned Lean 4.32.0 compiler
in 0.31 seconds. All five theorem axiom audits and three callers pass.
The callers check the existing `PowerSets` interface, the closed
`sealF Pow_form` statement and composition from EncBundle models to
quotient `Pow_form`. Dependencies are limited to `propext`,
`Classical.choice` and `Quot.sound`; no admissions or custom axioms occur.
An independent theory-agent read found no defect in the matrix resource,
trace bound, quotient coverage or formula bridge. Commands and results
are in `results/quotient-power-verification.json`.
