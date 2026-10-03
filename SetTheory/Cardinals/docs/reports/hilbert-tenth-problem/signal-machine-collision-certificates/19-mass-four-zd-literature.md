# Finite-mass conservative cellular automata: higher-dimensional literature check

Checked 2026-10-03. Target: translation-invariant deterministic finite-radius CAs on Z^d, d≥2, with a finite nonnegative-integer weighted alphabet, a unique weight-zero vacuum, at most one weight-one symbol, and total initial mass at most four. Particle count below means conserved mass unless explicitly identified as an agent/pebble count.

## Bottom line

This search did **not locate a primary theorem settling reachability for this exact class at mass ≤4**, or a verified counterexample under all its hypotheses. This is a bounded literature-search result, **not a novelty claim**. There is unusually close older literature on two-pebble automata; it should be discussed rather than claiming that the higher-dimensional question has no predecessors.

## Closest primary sources

### 1. Delorme–Mazoyer: planar two/three-pebble threshold

Marianne Delorme and Jacques Mazoyer, *Pebble Automata. Figures Families Recognition and Universality*, Fundamenta Informaticae 52(1–3) (2002), 81–132. [Publisher DOI](https://doi.org/10.3233/FUN-2002-521-305)

The publisher's abstract describes pebble automata on the unbounded plane Z², a recognition hierarchy collapsing at three pebbles, an intrinsically universal three-pebble automaton, and absence of intrinsically universal two-pebble automata. The full 2002 article was not retrieved. A 1999 predecessor is ENS Lyon Technical Report 32, cited by later authors.

Scope: one finite-state moving head plus passive movable pebbles, not an arbitrary conservative CA. Intrinsic universality and exact-configuration reachability are different questions. Under a straightforward unique-unit-symbol encoding, a stateful head needs at least mass two; three pebbles add at least three, giving at least mass five. This accounting is an inference, not the paper's theorem; labeled pebbles may require additional encoding work.

### 2. Lacalle–Gajardo: detailed two-pebble dynamics, with an explicit Z^d extension remark

Camilo Lacalle and Anahí Gajardo, *Revisiting of 2-pebble automata from a dynamical approach*, CI²MA prepublication 2014-15. [Full primary preprint](https://www.ci2ma.udec.cl/pdf/pre-publicaciones2/2014/pp14-15.pdf)

Full text checked; its displayed publication status is a submitted manuscript. It studies one-symbol grids, hence no input scenery carrying extra information. Pebbles are individually distinguishable (Definition §2.1).

- Lemma 3.1, printed pp.4–5, gives eventual periodicity of one-pebble motion. Its proof supports the n³ transient-plus-period bound from a local encounter/carrying start; do not apply that numerical bound to arbitrary distant initial head/pebble placement.
- Lemma 5.3, p.8, controls escape from a discrete ray by a bounded drifting window: after a suitable doubled-radius separation, later motion along that drift cannot return to the smaller neighborhood of the ray.
- Theorem 6.1, p.17: traces of two-pebble machines admit real-time recognition by a two-counter machine. This is **not** a reachability decidability theorem.
- The conclusion, p.17, explicitly says the geometric argument and results remain valid on Z^d.

Useful proof machinery, but a reduction covering CA cluster splitting, fusion, and transfer of finite control still has to be supplied.

### 3. Blum–Sakoda: a very small planar universal agent system

Manuel Blum and William J. Sakoda, *On the Capability of Finite Automata in 2 and 3 Dimensional Space*, FOCS 1977, 147–161; DOI 10.1109/SFCS.1977.20. [Author/institution-hosted reprint](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1978/ERL-m-78-35.pdf)

Printed p.148 states that two finite automata plus one pebble on an unobstructed planar checkerboard simulate a universal two-counter automaton; attribution is to Sipser, personal communication (1977). The same page states that one finite automaton with two pebbles cannot explore a whole half-plane and cannot be universal. The latter is reported there rather than developed into a complete reachability algorithm.

This is a relevant potential counterexample to an unrestricted *three-agent* claim. It is not a mass-four counterexample with a unique unit symbol: two independently stateful agents plus a pebble have naive minimum mass 2+2+1=5. The paper also discusses a single universal walker on a plane with both axes marked; those infinite axes violate the finite-mass vacuum setup.

### 4. Salo–Törmä: independent heads and sparse-input computational power

Ville Salo and Ilkka Törmä, *Plane-Walking Automata* (2014 preprint). [Author PDF](https://villesalo.com/article/PWA.pdf), [arXiv](https://arxiv.org/abs/1408.6701)

The model has independently controlled synchronous heads communicating only when colocated. Proposition 3 (pp.10–11) uses two heads and two static input marks to recognize a co-RE-complete sparse subshift; the simulation uses an input mark as an origin and one head as a moving counter endpoint. Theorem 5 gives the three-head hierarchy collapse in every dimension.

These heads read a separate supplied configuration. Its marked cells are not automatically free in a conservative-CA encoding. Two stateful heads already have naive mass at least four; the extra static marks raise it further. Thus the sparse-input result must not be cited as a two- or four-particle counterexample. The authors' later [Independent finite automata on Cayley graphs](https://doi.org/10.1007/s11047-017-9613-6) generalizes this research program.

## Conservative CA constructions and important exclusions

### 5. Morita–Tojima–Imai–Ogiro (2002), genuinely two-dimensional

*Universal Computing in Reversible and Number-Conserving Two-Dimensional Cellular Spaces*, in *Collision-Based Computing*, pp.161–199. [Publisher chapter](https://link.springer.com/chapter/10.1007/978-1-4471-0129-1_7)

Publisher abstract verified: two types of 2D number-conserving reversible CA are described, using Fredkin gates or rotary elements; the latter simulate reversible two-counter machines. Full chapter not retrieved. The accessible abstract gives neither a ≤4 total-mass bound nor the unique-unit-symbol restriction. This establishes relevant 2D universality, not the requested threshold.

### 6. Schaeffer (2014): physical universality is not unbounded finite-seed computation

Luke Schaeffer, *A Physically Universal Cellular Automaton*, ECCC TR14-084. [Full primary preprint](https://eccc.weizmann.ac.il/report/2014/084/download/), [author's model explanation](https://lukeschaeffer.com/projects/physCA/)

Full text checked. The 2D particle model is number conserving. Theorem 4 (Diffusion Theorem, pp.9–10) controls the escape of finite configurations; the discussion on p.18 explicitly notes that the theorem bounds the duration of computation from a finite initial configuration. Thus this physical-universality construction supplies no small-finite-seed Turing-universality counterexample. Its standard CA/block encodings also require care: different velocity tracks or Margolus block phases cannot be silently identified with one ordinary translation-invariant unit-mass state.

### 7. The supplied one-dimensional precursor: Kong (2021)

Gil-Tak Kong, *A hierarchical structural interpretation of 1-dimensional 2-state number conserving cellular automata*, PhD thesis, §2.4, printed pp.12–15. [Full primary thesis](https://hiroshima.repo.nii.ac.jp/record/2002360/files/k8621_3.pdf)

Full text checked. The section concerns binary one-dimensional NCCAs. It states eventual periodicity for two particles and non-strong-Turing-universality for three, with four left open in its conclusion. It does not establish a higher-dimensional or weighted-alphabet result, or explicitly prove uniform reachability decidability.

Bibliographic caution: its attribution of the five-particle upper bound uses reference [13], but that bibliography entry is Imai–Alhazov's 2010 radius-1/2 paper. The separately identifiable paper is Artiom Alhazov and Katsunobu Imai, *Particle Complexity of Universal Finite Number-Conserving Cellular Automata*, CANDAR 2016, 209–214, [DOI](https://doi.org/10.1109/CANDAR.2016.0045). Its full text was not obtained in this pass, so details of its construction were not independently reverified here.

## Guardrails for using these findings

1. Count the head/control, passive markers, scaffolding, phase tracks, and nonzero input marks; counting only moving objects can hide mass.
2. A unique weight-zero vacuum excludes free infinite axes, obstacles, or tape symbols.
3. A single weight-one symbol excludes assigning freely many control states or velocities to individual mass-one particles.
4. A finite configuration is not the same as a uniform mass bound of four over all encoded inputs.
5. Nonuniversality, failure to explore the plane, and trace recognizability are not automatically decidable reachability.
6. A reduction from all low-mass CAs to a pebble model needs to preserve collision-mediated control changes, splitting/fusion, and synchronous motion. None of the retrieved sources supplies that reduction for the exact requested class.

## Reading copies

No copyrighted primary-source PDFs are redistributed. Follow the primary links above.
