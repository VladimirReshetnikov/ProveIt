# Publication-reader correction

The first publication metadata controls passed 10 positive and 34 rejection cases. The first collection then stopped before writing a packet: its additional compatibility-profile assertion incorrectly required `Classical.choice` for `ZFNativeCompat12.models`. The actual compiler log and frozen final map correctly report only `propext` and `Quot.sound` for that theorem.

The corrected reader requires all three standard axioms for the three `WFModelCompat12` clients, exactly those two axioms for `ZFNativeCompat12.models`, and all three standard axioms for its six remaining clients. It retains the existing positive two-axiom control and adds rejection of an extra `Classical.choice`. The successor controls passed 10 positive and 35 rejection cases; collection and saved review with current-source checking then both exited successfully.

The archive retains the entire first helper/configuration freeze, controls, raw failed traceback and outer record. The successor source peer and successful publication execution records are adjacent. This was an overstrict publication-reader assertion; neither Lean run failed or was repeated. No producer or supplied renderer was rerun to repair it.
