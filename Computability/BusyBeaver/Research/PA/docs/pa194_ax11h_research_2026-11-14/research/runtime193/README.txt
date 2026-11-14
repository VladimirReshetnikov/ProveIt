RUNTIME193 REPAIR SEARCH: RESULTS AND REPRODUCTION

No accepted 193-state blank-start consistency machine was obtained.
This directory contains negative research evidence, not a positive machine.
See results.json for counts, exact scope, and limitations.

The old 193-state core is inherited from the packet pa_sub194_research_2026-11-13.zip
at ProveIt commit 1c9524d8bf2e0a27b9a16ff622359927f536e663. In native numbering it
merges 301 into 88 and changes 88/0 to 0L51 and 51/0 to 0R122. It has a universal
source-step certificate on canonical source frames (4,780 outcomes), but its
unchanged blank startups are known to halt or escape along an outward ray.
Thus runtime193.native.tm is a REJECTED blank-start construction.

The prior AX11 incoming packet already screened pairs/triples of 327 particular
outside-arithmetic-box candidate detours. The new main screen here extends to
four distinct transition-row changes, and permits a smaller header offset 36
instead of 48. A hit would have required a fresh complete source verification;
individual candidate neutrality is not assumed to survive composition.

Fresh results:
- All 193 starts, scheduler entry sites 25..44, through 20,000 transitions:
  5,544,509 eligible quadruple/start cases, 6,106,954 runs including preparations,
  79,714,470,105 transitions, zero complete frames. 3,983,144 runs reached a bound.
- Start 74, all 3,673 source sites, through 20,000 transitions:
  106,694 quadruples, 119,534 total runs, 1,093,967,014 transitions, zero frames.
- With append-zero variant 198/0=0L40, start 74 and all 3,673 sites:
  103,375 quadruples, 115,953 total runs, 969,547,469 transitions, zero frames.
The quadruple counts use trajectory row-encounter filters and de-duplicate
quadruple/start pairs. They are not the number of all formal four-element
subsets. All preparatory phases include all starts. The offset 36 criterion
is deliberately more permissive; no universal runtime theorem at 36 is claimed.

Build and run the all-start scheduler-entry experiment, from this directory:
  g++ -O3 -std=c++17 quad_startup.cpp -o quad_startup
  ./quad_startup runtime193.native.tm safe_edits.tsv scheduler_templates.tsv 6 20000

All-source-site experiment from native start 74:
  g++ -O3 -std=c++17 quad_allframes.cpp -o quad_allframes
  ./quad_allframes runtime193.native.tm safe_edits.tsv all_source_templates.tsv 5 20000

The last argument is literal step bound; stage 5 examines four-row edits at 74,
whereas stage 6 examines them at every native working control. The earlier
preparatory single-edit phase is shared, not disjoint additional evidence.
The all-start run took approximately six minutes in the research environment.

The independent guard search used radius 12 contexts of two sensitive decoder
rows. Unlike the fixed detour pool, it allowed an arbitrary changed first row
and an arbitrary changed non-box row encountered on the resulting first test
trajectory. Of 8,544,225 tested pairs, 31 passed their targeted local windows;
all 31 were rejected by the full 4,780-outcome source checker. The closest pair
replaces 122/0 by 0L174 and 174/0 by 0R30 (or 0R47); it fails at source site 3554,
the zero branch of a decrement of logical continuation register L.

Reproduce the exact contexts and guard search:
  python collect_guard_contexts.py 12 fresh-contexts12.txt
  g++ -O3 -std=c++17 guard_synthesis.cpp -o guard_synthesis
  ./guard_synthesis runtime193.native.tm 12 128 fresh-contexts12.txt 122 0 > fresh122.out
  ./guard_synthesis runtime193.native.tm 12 128 fresh-contexts12.txt 137 0 > fresh137.out
  python validate_guards.py fresh122.out replay122
  python validate_guards.py fresh137.out replay137

The local screen compares a candidate path with the first 64 original local
steps, permitting at most 128 candidate steps and no excursion outside its
radius 12 window. It is a nomination screen, not an equivalence theorem. Full
source checking is essential; the 31 rejected survivors demonstrate why.

The inherited executable symbolic checker uses generic arithmetic-box lemmas.
It is not a newly compiled Lean or iPRA formalization. The changes screened
here do not fix the independent outstanding consistency-calibration proof.

None of these bounded failures is a general lower bound on Turing machines.
In particular, limit exits remain unresolved and arbitrary other transition
edits, tape encodings, theories, and source compilers remain outside the search.

Third-party runtime/compiler material is retained in vendor/ with notices
in licenses/. Newly written research scripts are included as source only.
