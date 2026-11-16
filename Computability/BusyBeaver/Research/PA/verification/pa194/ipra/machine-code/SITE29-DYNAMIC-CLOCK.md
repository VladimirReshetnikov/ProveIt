# Exact physical clock for site 29

`PA194Site29DynamicClock.exactClock` gives the literal machine step count for the site 29 to site 30 segment in every PRA model. The register file has the stated repeated one-valued spare-block suffix, and its count may be nonstandard. The theorem gives a model-valued clock formula; [the clock-code theorem](SITE29-CLOCK-CODE.md) supplies a primitive-recursive code for it.

The repository staged replay using `check-site29-dynamic-clock.sh` exited successfully and reported no `sorryAx`. It recompiles the pinned site 29 source suffix against selected pinned prebuilt machine objects and retained project and package foundations; it does not rebuild the complete transitive source closure. The checker records its required input paths and verifies source and selected object hashes. This segment alone does not establish a consistency direction.
