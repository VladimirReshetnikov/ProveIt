# Independent prelaunch review: three symbolic-mask isolation checks

**Three separate GOs, one coordinated author run per exact packet.** No Lean was run by this review. Source scopes were reviewed in `reviews/trace74-symbolic-mask-isolation-draft-independent/`.

- FixedRadix source SHA-256 `079d6a935908d678212dca47d418aee5ad94ff3ab2c6b164f90f89e2e8778d71`, runner `a53744dfd4cac72f440697323274d21208812a521a13ebe70ad9f3851efc8859`, outer `a2999f5dc0e86c460bfae89162c1be33daead75c2aaf36284f3dad372c7b1c5d` selects the checked GenericDefect object and exact `Trace74FixedRadix.low_add_defect` report.
- FixedIndices source SHA-256 `b9f1ade6b0fdf8c8bff2c5fde6ccf8845671f9842157eb86260641894075e989`, runner `ea502c188b442b568aa392e4bed120a5d9ac85817380f264710d63d3f09a127f`, outer `470d2ba06a9466f2ac78e669d7319c05f8f1da1a792ba0a53d4fa88c38cd4f15` selects the same checked GenericDefect object and exact `Trace74FixedIndices.low_add_defect` report.
- LowNatDefinition source SHA-256 `e05dec25774e6f1806b2c85d5f036180a2b20367f2554f7ef35d17f58151d5fe`, runner `1ed9fc2962433b9d534528f942dc17f6eb834c7a9f7bb9b41626f7e3bc83fc4c`, outer `58be8dd6f4c5f287854054fca56b02fe33b6339797d8f2bfbd7762d0fbbc7ba4` selects CompactSymbolicPorts and exact `Trace74LowNatDefinition.low_nat_definition` report.

Independent actual read-only preflights passed 2036/81/1, 2036/81/1 and 2035/81/1, respectively, with exact source and current first-selected direct providers, parent union/companions and retained closure guards checked. Each copied actual-function policy and copied-supervisor suite independently reproduced 25 and six controls. Supervisors bind runner/preflight/policy and child exit/PASS; actual outer tool exits require separate capture. Resource/no-clobber/source-copy and named standard-axiom/no-axiom report checks remain in place.

Each is an isolated diagnostic, not a joined mask-cover proof. Tactic/runtime behavior is not known until author checks. Four inherited baseline nodes and project/package/dynamic/transitive ancestry remain subject to prior limitations; no external file binding, 74 graph guard or iPRA endpoint follows.
