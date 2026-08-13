#!/usr/bin/env python3
"""Generate bounded kernel certificates for the transitive subgroups of S5.

The old all-at-once classification certificate explored all 120 possible
second generators for 120 breadth steps.  This generator records the eight
double cosets of the standard C5 in S5 and emits independent Lean modules for
their cover and their short generation computations.

Python is not part of the proof.  Every emitted proposition is checked again
by Lean's ordinary ``decide`` evaluator.  The Python model is deliberately
validated before rendering so that stale or internally inconsistent generated
data fails early and deterministically.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from dataclasses import dataclass
from pathlib import Path


Permutation = tuple[int, int, int, int, int]

ROOT = Path(__file__).resolve().parents[3]
LEAN_DIR = ROOT / "Algebra/PolynomialFormulas/Lean/PolynomialFormulas"
GENERATOR = "Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py"
NAMESPACE = (
    "LeanProofs.PolynomialFormulas."
    "Fin5TransitiveClassificationCertificates"
)

IDENTITY: Permutation = (0, 1, 2, 3, 4)
FIVE_CYCLE: Permutation = (1, 2, 3, 4, 0)


def compose(left: Permutation, right: Permutation) -> Permutation:
    """Lean/Mathlib permutation multiplication: ``(left * right) i``."""
    return tuple(left[right[index]] for index in range(5))  # type: ignore[return-value]


def inverse(permutation: Permutation) -> Permutation:
    result = [0] * 5
    for index, image in enumerate(permutation):
        result[image] = index
    return tuple(result)  # type: ignore[return-value]


def power(permutation: Permutation, exponent: int) -> Permutation:
    result = IDENTITY
    base = permutation
    while exponent:
        if exponent & 1:
            result = compose(result, base)
        base = compose(base, base)
        exponent //= 2
    return result


def swap(left: int, right: int) -> Permutation:
    result = list(IDENTITY)
    result[left], result[right] = result[right], result[left]
    return tuple(result)  # type: ignore[return-value]


def sign(permutation: Permutation) -> int:
    inversions = sum(
        permutation[left] > permutation[right]
        for left in range(5)
        for right in range(left + 1, 5)
    )
    return 1 if inversions % 2 == 0 else -1


def affine(multiplier: int, offset: int) -> Permutation:
    return tuple(
        (multiplier * index + offset) % 5 for index in range(5)
    )  # type: ignore[return-value]


def permutation_code(permutation: Permutation) -> int:
    """Base-five encoding mirrored by the generated Lean ``permCode``."""
    return sum(image * 5**index for index, image in enumerate(permutation))


ALL_PERMUTATIONS = frozenset(itertools.permutations(range(5)))
C5 = frozenset(power(FIVE_CYCLE, exponent) for exponent in range(5))
D5 = frozenset(
    affine(multiplier, offset)
    for multiplier in (1, 4)
    for offset in range(5)
)
F20 = frozenset(
    affine(multiplier, offset)
    for multiplier in (1, 2, 3, 4)
    for offset in range(5)
)
A5 = frozenset(permutation for permutation in ALL_PERMUTATIONS if sign(permutation) == 1)


CLASS_ELEMENTS: dict[str, frozenset[Permutation]] = {
    "cyclic": C5,
    "dihedral": D5,
    "frobenius": F20,
    "alternating": A5,
    "symmetric": ALL_PERMUTATIONS,
}


@dataclass(frozen=True)
class Representative:
    lean_name: str
    lean_expression: str
    images: Permutation
    class_name: str
    depth: int
    double_coset_card: int
    checkpoint_depth: int | None = None


MULTIPLIER_TWO: Permutation = (0, 2, 4, 1, 3)
REFLECTION: Permutation = (0, 4, 3, 2, 1)

REPRESENTATIVES: tuple[Representative, ...] = (
    Representative("cyclic", "1", IDENTITY, "cyclic", 2, 5),
    Representative("dihedral", "reflection", REFLECTION, "dihedral", 3, 5),
    Representative(
        "frobenius0", "multiplierTwo", MULTIPLIER_TWO, "frobenius", 3, 5
    ),
    Representative(
        "frobenius1",
        "multiplierTwo⁻¹",
        inverse(MULTIPLIER_TWO),
        "frobenius",
        3,
        5,
    ),
    Representative(
        "alternating0",
        "Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4",
        compose(swap(2, 3), swap(3, 4)),
        "alternating",
        6,
        25,
        3,
    ),
    Representative(
        "alternating1",
        "Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4",
        compose(swap(1, 2), swap(3, 4)),
        "alternating",
        9,
        25,
        5,
    ),
    Representative(
        "symmetric0",
        "Equiv.swap (3 : Fin 5) 4",
        swap(3, 4),
        "symmetric",
        10,
        25,
        5,
    ),
    Representative(
        "symmetric1",
        "Equiv.swap (2 : Fin 5) 4",
        swap(2, 4),
        "symmetric",
        10,
        25,
        5,
    ),
)

EXPECTED_STAGE_SIZES: tuple[tuple[int, ...], ...] = (
    (1, 3, 5),
    (1, 4, 8, 10),
    (1, 5, 16, 20),
    (1, 5, 16, 20),
    (1, 5, 15, 34, 51, 59, 60),
    (1, 4, 10, 18, 28, 38, 48, 56, 59, 60),
    (1, 4, 10, 20, 36, 60, 89, 110, 116, 119, 120),
    (1, 4, 10, 20, 36, 60, 89, 110, 116, 119, 120),
)


def generation_step(
    generator: Permutation, stage: frozenset[Permutation]
) -> frozenset[Permutation]:
    letters = generation_letters(generator)
    return stage | frozenset(
        compose(letter, element) for letter in letters for element in stage
    )


def generation_letters(generator: Permutation) -> tuple[Permutation, ...]:
    return (FIVE_CYCLE, inverse(FIVE_CYCLE), generator, inverse(generator))


def structural_step_additions(
    generator: Permutation,
    source: frozenset[Permutation],
    target: frozenset[Permutation],
) -> tuple[frozenset[Permutation], ...]:
    """Partition newly reached rows by a deterministic inverse witness."""
    letters = generation_letters(generator)
    require(source <= target, "a generation step must retain its source")
    require(
        generation_step(generator, source) == target,
        "structural step target must equal the Python generation step",
    )
    buckets: list[set[Permutation]] = [set() for _ in letters]
    for element in sorted(target - source, key=permutation_code):
        for bucket_index, letter in enumerate(letters):
            predecessor = compose(inverse(letter), element)
            if predecessor in source:
                buckets[bucket_index].add(element)
                break
        else:
            raise RuntimeError(
                "classification model validation failed: "
                "new generation row has no inverse witness"
            )
    result = tuple(frozenset(bucket) for bucket in buckets)
    require(
        frozenset().union(*result) == target - source,
        "inverse-witness buckets must cover exactly the new rows",
    )
    require(
        all(
            result[left].isdisjoint(result[right])
            for left in range(len(result))
            for right in range(left + 1, len(result))
        ),
        "inverse-witness buckets must be pairwise disjoint",
    )
    require(
        all(
            compose(inverse(letter), element) in source
            for letter, bucket in zip(letters, result, strict=True)
            for element in bucket
        ),
        "every emitted inverse witness must lie in the source stage",
    )
    require(
        all(
            compose(letter, element) in target
            for letter in letters
            for element in source
        ),
        "every generator letter must preserve the target-stage upper bound",
    )
    return result


def iterate_generation_step(
    generator: Permutation, seed: frozenset[Permutation], steps: int
) -> frozenset[Permutation]:
    result = seed
    for _ in range(steps):
        result = generation_step(generator, result)
    return result


def generated_stage(generator: Permutation, depth: int) -> frozenset[Permutation]:
    return iterate_generation_step(generator, frozenset({IDENTITY}), depth)


def double_coset(representative: Permutation) -> frozenset[Permutation]:
    return frozenset(
        compose(compose(left, representative), right)
        for left in C5
        for right in C5
    )


def element_class(permutation: Permutation) -> str:
    if permutation in C5:
        return "cyclic"
    if permutation in D5:
        return "dihedral"
    if permutation in F20:
        return "frobenius"
    if sign(permutation) == 1:
        return "alternating"
    return "symmetric"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(f"classification model validation failed: {message}")


def validate_model() -> None:
    require(len(ALL_PERMUTATIONS) == 120, "S5 must contain 120 permutations")
    require(
        all(
            sorted(permutation) == list(range(5))
            for permutation in ALL_PERMUTATIONS
        ),
        "every enumerated row must be a permutation",
    )
    require(
        len({permutation_code(g) for g in ALL_PERMUTATIONS}) == 120,
        "base-five permutation codes must be injective",
    )
    require(
        tuple(map(len, (C5, D5, F20, A5, ALL_PERMUTATIONS)))
        == (5, 10, 20, 60, 120),
        "class carrier sizes must be 5, 10, 20, 60, 120",
    )
    require(
        C5 <= D5 <= F20 <= ALL_PERMUTATIONS,
        "the standard affine subgroup tower must be nested",
    )
    require(
        REPRESENTATIVES[1].images == REFLECTION,
        "the dihedral representative must be reflection",
    )
    require(
        REPRESENTATIVES[2].images == MULTIPLIER_TWO,
        "the first Frobenius representative must multiply by two",
    )
    require(
        REPRESENTATIVES[3].images == inverse(MULTIPLIER_TWO),
        "the second Frobenius representative must be its inverse",
    )

    cosets = [double_coset(representative.images) for representative in REPRESENTATIVES]
    require(
        [len(coset) for coset in cosets]
        == [
            representative.double_coset_card
            for representative in REPRESENTATIVES
        ],
        "double-coset cardinalities must match the emitted table",
    )
    require(
        all(
            cosets[left].isdisjoint(cosets[right])
            for left in range(8)
            for right in range(left + 1, 8)
        ),
        "the eight double cosets must be pairwise disjoint",
    )
    require(
        frozenset().union(*cosets) == ALL_PERMUTATIONS,
        "the eight double cosets must exhaust S5",
    )
    require(
        frozenset().union(*(cosets[index] for index in (0, 1, 4, 5)))
        == A5,
        "the four even double cosets must exhaust A5",
    )
    require(
        frozenset().union(*(cosets[index] for index in (2, 3, 6, 7)))
        == (ALL_PERMUTATIONS - A5),
        "the four odd double cosets must exhaust the complement of A5",
    )

    for index, representative in enumerate(REPRESENTATIVES):
        target = CLASS_ELEMENTS[representative.class_name]
        stage_sizes = tuple(
            len(generated_stage(representative.images, depth))
            for depth in range(representative.depth + 1)
        )
        require(
            stage_sizes == EXPECTED_STAGE_SIZES[index],
            f"generation-stage sizes differ for row {index}",
        )
        require(
            all(
                element_class(element) == representative.class_name
                for element in cosets[index]
            ),
            f"double-coset class is not constant for row {index}",
        )
        require(
            generated_stage(representative.images, representative.depth) == target,
            f"generation does not reach the class carrier for row {index}",
        )
        require(
            generated_stage(representative.images, representative.depth - 1)
            != target,
            f"emitted generation depth is not minimal for row {index}",
        )
        if representative.checkpoint_depth is not None:
            checkpoint = generated_stage(
                representative.images, representative.checkpoint_depth
            )
            require(
                iterate_generation_step(
                    representative.images,
                    checkpoint,
                    representative.depth - representative.checkpoint_depth,
                )
                == target,
                f"checkpoint does not finish at the target for row {index}",
            )
            checkpoint_codes = {permutation_code(g) for g in checkpoint}
            require(
                {
                    g
                    for g in ALL_PERMUTATIONS
                    if permutation_code(g) in checkpoint_codes
                }
                == checkpoint,
                f"checkpoint codes do not decode exactly for row {index}",
            )
            require(
                len(checkpoint_codes)
                == EXPECTED_STAGE_SIZES[index][representative.checkpoint_depth],
                f"checkpoint cardinality differs for row {index}",
            )
            if representative.class_name == "symmetric":
                for depth in range(representative.depth):
                    structural_step_additions(
                        representative.images,
                        generated_stage(representative.images, depth),
                        generated_stage(representative.images, depth + 1),
                    )


def generated_header() -> str:
    return (
        "/-\n"
        "This file is generated.  Do not edit it directly.\n\n"
        f"Regenerate with `{GENERATOR}` and verify with\n"
        f"`{GENERATOR} --check`.  Python supplies data only; every theorem\n"
        "below is checked by Lean using ordinary kernel reduction.\n"
        "-/\n\n"
    )


def render_nat_list(codes: list[int], indent: str = "  ") -> str:
    chunks = [codes[index : index + 10] for index in range(0, len(codes), 10)]
    lines = []
    for chunk_index, chunk in enumerate(chunks):
        prefix = "[" if chunk_index == 0 else " "
        suffix = "," if chunk_index + 1 < len(chunks) else "]"
        lines.append(indent + prefix + ", ".join(map(str, chunk)) + suffix)
    return "\n".join(lines)


def render_code_finset_definition(name: str, codes: list[int]) -> str:
    if not codes:
        return f"def {name} : Finset ℕ := ∅\n"
    return f"""def {name} : Finset ℕ :=
{render_nat_list(codes)}.toFinset
"""


def render_data_module() -> str:
    representative_expressions = ",\n    ".join(
        representative.lean_expression for representative in REPRESENTATIVES
    )
    representative_classes = ", ".join(
        f".{representative.class_name}" for representative in REPRESENTATIVES
    )
    depths = ", ".join(str(representative.depth) for representative in REPRESENTATIVES)
    cards = ", ".join(
        str(representative.double_coset_card) for representative in REPRESENTATIVES
    )
    return generated_header() + f"""import PolynomialFormulas.Fin5DihedralCore
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace {NAMESPACE}

open Equiv

abbrev S5 := Fin5DihedralCore.S5
abbrev fiveCycle : S5 := Fin5DihedralCore.fiveCycle
abbrev reflection : S5 := Fin5DihedralCore.reflection
abbrev multiplierTwo : S5 := FrobeniusDummitResolvent.multiplierTwo
abbrev standardC5 : Subgroup S5 := Fin5DihedralCore.standardC5
abbrev standardD5 : Subgroup S5 := Fin5DihedralCore.standardD5
abbrev standardF20 : Subgroup S5 := Fin5Solvable.standardF20
abbrev c5Elements : Finset S5 := Fin5DihedralCore.c5Elements
abbrev d5Elements : Finset S5 := Fin5DihedralCore.d5Elements
abbrev f20Elements : Finset S5 := Fin5TransitiveC5.f20Elements

def evenElements : Finset S5 :=
  Finset.univ.filter (fun g ↦ Equiv.Perm.sign g = 1)

def oddElements : Finset S5 :=
  Finset.univ.filter (fun g ↦ Equiv.Perm.sign g ≠ 1)

inductive GeneratedClass
  | cyclic
  | dihedral
  | frobenius
  | alternating
  | symmetric
  deriving DecidableEq, Fintype, Repr

def classElements : GeneratedClass → Finset S5
  | .cyclic => c5Elements
  | .dihedral => d5Elements
  | .frobenius => f20Elements
  | .alternating => evenElements
  | .symmetric => Finset.univ

/-- One representative for each `C5` double coset in `S5`. -/
def representative : Fin 8 → S5 := ![
    {representative_expressions}]

def representativeClass : Fin 8 → GeneratedClass :=
  ![{representative_classes}]

def representativeDepth : Fin 8 → ℕ :=
  ![{depths}]

def representativeDoubleCosetCard : Fin 8 → ℕ :=
  ![{cards}]

/-- The five-class membership bucket used by normalized classification. -/
def elementClass (g : S5) : GeneratedClass :=
  if g ∈ c5Elements then .cyclic
  else if g ∈ d5Elements then .dihedral
  else if g ∈ f20Elements then .frobenius
  else if Equiv.Perm.sign g = 1 then .alternating
  else .symmetric

/-- The finite double coset `C5 * representative i * C5`. -/
def doubleCosetElements (i : Fin 8) : Finset S5 :=
  (Finset.univ : Finset (Fin 5 × Fin 5)).image (fun ab ↦
    fiveCycle ^ (ab.1 : ℕ) * representative i *
      fiveCycle ^ (ab.2 : ℕ))

/-- Injective base-five code on permutations of five letters. -/
def permCode (g : S5) : ℕ :=
  (g 0).val + 5 * (g 1).val + 25 * (g 2).val +
    125 * (g 3).val + 625 * (g 4).val

/-- Reconstruct an explicit finite permutation table from generated codes. -/
def elementsWithCodes (codes : Finset ℕ) : Finset S5 :=
  Finset.univ.filter (fun g ↦ permCode g ∈ codes)

end {NAMESPACE}
"""


def render_generation_core() -> str:
    return generated_header() + f"""import PolynomialFormulas.Fin5TransitiveClassificationCertificateData

namespace {NAMESPACE}

/-- One breadth step using the standard rotation and a second generator. -/
def generationStep (g : S5) (stage : Finset S5) : Finset S5 :=
  stage ∪ stage.image (fun x ↦ fiveCycle * x) ∪
    stage.image (fun x ↦ fiveCycle⁻¹ * x) ∪
    stage.image (fun x ↦ g * x) ∪
    stage.image (fun x ↦ g⁻¹ * x)

def iterateGenerationStep (g : S5) (seed : Finset S5) : ℕ → Finset S5
  | 0 => seed
  | n + 1 => generationStep g (iterateGenerationStep g seed n)

def generatedStage (g : S5) (n : ℕ) : Finset S5 :=
  iterateGenerationStep g {{1}} n

theorem iterateGenerationStep_add (g : S5) (seed : Finset S5) (m n : ℕ) :
    iterateGenerationStep g seed (m + n) =
      iterateGenerationStep g (iterateGenerationStep g seed m) n := by
  induction n with
  | zero => simp [iterateGenerationStep]
  | succ n ih =>
      rw [Nat.add_succ, iterateGenerationStep, iterateGenerationStep, ih]

theorem generatedStage_add (g : S5) (m n : ℕ) :
    generatedStage g (m + n) =
      iterateGenerationStep g (generatedStage g m) n := by
  simpa only [generatedStage] using
    iterateGenerationStep_add g ({{1}} : Finset S5) m n

theorem generationStep_subset_subgroup
    (H : Subgroup S5) (g : S5)
    (hfive : fiveCycle ∈ H) (hg : g ∈ H)
    (stage : Finset S5) (hstage : ∀ x ∈ stage, x ∈ H) :
    ∀ x ∈ generationStep g stage, x ∈ H := by
  intro x hx
  simp only [generationStep, Finset.mem_union] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx)
  · exact hstage x hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem hfive (hstage y hy)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem (H.inv_mem hfive) (hstage y hy)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem hg (hstage y hy)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem (H.inv_mem hg) (hstage y hy)

theorem iterateGenerationStep_subset_subgroup
    (H : Subgroup S5) (g : S5)
    (hfive : fiveCycle ∈ H) (hg : g ∈ H)
    (seed : Finset S5) (hseed : ∀ x ∈ seed, x ∈ H) :
    ∀ n x, x ∈ iterateGenerationStep g seed n → x ∈ H := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact hseed x hx
  | succ n ih =>
      exact generationStep_subset_subgroup H g hfive hg
        (iterateGenerationStep g seed n) ih

theorem generatedStage_subset_subgroup
    (H : Subgroup S5) (g : S5)
    (hfive : fiveCycle ∈ H) (hg : g ∈ H) :
    ∀ n x, x ∈ generatedStage g n → x ∈ H := by
  intro n x hx
  apply iterateGenerationStep_subset_subgroup H g hfive hg
    ({{1}} : Finset S5) (by
      intro y hy
      have hy' : y = 1 := by simpa using hy
      subst y
      exact H.one_mem) n x
  exact hx

end {NAMESPACE}
"""


def render_even_cover() -> str:
    return generated_header() + f"""import PolynomialFormulas.Fin5TransitiveClassificationCertificateData

namespace {NAMESPACE}

def evenDoubleCosets : Finset S5 :=
  ((doubleCosetElements 0 ∪ doubleCosetElements 1) ∪
    doubleCosetElements 4) ∪ doubleCosetElements 5

set_option maxRecDepth 100000 in
theorem even_doubleCoset_cover_certificate :
    evenDoubleCosets = evenElements := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_0_card_certificate :
    (doubleCosetElements 0).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_1_card_certificate :
    (doubleCosetElements 1).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_4_card_certificate :
    (doubleCosetElements 4).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_5_card_certificate :
    (doubleCosetElements 5).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_0_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 0 → elementClass g = .cyclic := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_1_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 1 → elementClass g = .dihedral := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_4_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 4 → elementClass g = .alternating := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_5_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 5 → elementClass g = .alternating := by
  decide

end {NAMESPACE}
"""


def render_odd_cover() -> str:
    return generated_header() + f"""import PolynomialFormulas.Fin5TransitiveClassificationCertificateData

namespace {NAMESPACE}

def oddDoubleCosets : Finset S5 :=
  ((doubleCosetElements 2 ∪ doubleCosetElements 3) ∪
    doubleCosetElements 6) ∪ doubleCosetElements 7

set_option maxRecDepth 100000 in
theorem odd_doubleCoset_cover_certificate :
    oddDoubleCosets = oddElements := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_2_card_certificate :
    (doubleCosetElements 2).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_3_card_certificate :
    (doubleCosetElements 3).card = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_6_card_certificate :
    (doubleCosetElements 6).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_7_card_certificate :
    (doubleCosetElements 7).card = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_2_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 2 → elementClass g = .frobenius := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_3_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 3 → elementClass g = .frobenius := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_6_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 6 → elementClass g = .symmetric := by
  decide

set_option maxRecDepth 100000 in
theorem doubleCoset_7_class_certificate :
    ∀ g : S5, g ∈ doubleCosetElements 7 → elementClass g = .symmetric := by
  decide

end {NAMESPACE}
"""


def render_double_coset_aggregate() -> str:
    return generated_header() + f"""import PolynomialFormulas.Fin5TransitiveClassificationEvenCoverCertificate
import PolynomialFormulas.Fin5TransitiveClassificationOddCoverCertificate
import Mathlib.Tactic

namespace {NAMESPACE}

def allDoubleCosets : Finset S5 := evenDoubleCosets ∪ oddDoubleCosets

theorem all_doubleCoset_cover : allDoubleCosets = Finset.univ := by
  unfold allDoubleCosets
  rw [even_doubleCoset_cover_certificate, odd_doubleCoset_cover_certificate]
  ext g
  by_cases hsign : Equiv.Perm.sign g = 1 <;>
    simp [evenElements, oddElements, hsign]

theorem exists_doubleCoset_rep (g : S5) :
    ∃ i : Fin 8, g ∈ doubleCosetElements i := by
  have hg : g ∈ allDoubleCosets := by
    rw [all_doubleCoset_cover]
    simp
  simp only [allDoubleCosets, evenDoubleCosets, oddDoubleCosets,
    Finset.mem_union] at hg
  rcases hg with heven | hodd
  · rcases heven with ((h0 | h1) | h4) | h5
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨4, h4⟩
    · exact ⟨5, h5⟩
  · rcases hodd with ((h2 | h3) | h6) | h7
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨6, h6⟩
    · exact ⟨7, h7⟩

theorem doubleCoset_class (i : Fin 8) (g : S5)
    (hg : g ∈ doubleCosetElements i) :
    elementClass g = representativeClass i := by
  fin_cases i
  · exact doubleCoset_0_class_certificate g hg
  · exact doubleCoset_1_class_certificate g hg
  · exact doubleCoset_2_class_certificate g hg
  · exact doubleCoset_3_class_certificate g hg
  · exact doubleCoset_4_class_certificate g hg
  · exact doubleCoset_5_class_certificate g hg
  · exact doubleCoset_6_class_certificate g hg
  · exact doubleCoset_7_class_certificate g hg

theorem doubleCoset_card (i : Fin 8) :
    (doubleCosetElements i).card = representativeDoubleCosetCard i := by
  fin_cases i
  · exact doubleCoset_0_card_certificate
  · exact doubleCoset_1_card_certificate
  · exact doubleCoset_2_card_certificate
  · exact doubleCoset_3_card_certificate
  · exact doubleCoset_4_card_certificate
  · exact doubleCoset_5_card_certificate
  · exact doubleCoset_6_card_certificate
  · exact doubleCoset_7_card_certificate

/-- Every permutation is a left and right `C5` translate of one table row. -/
theorem exists_rotation_decomposition (g : S5) :
    ∃ i : Fin 8, ∃ a b : Fin 5,
      g = fiveCycle ^ (a : ℕ) * representative i * fiveCycle ^ (b : ℕ) ∧
      elementClass g = representativeClass i := by
  obtain ⟨i, hi⟩ := exists_doubleCoset_rep g
  have hclass := doubleCoset_class i g hi
  rw [doubleCosetElements] at hi
  obtain ⟨ab, _, hab⟩ := Finset.mem_image.mp hi
  exact ⟨i, ab.1, ab.2, hab.symm, hclass⟩

end {NAMESPACE}
"""


def render_affine_generation() -> str:
    rows = []
    for index in range(4):
        representative = REPRESENTATIVES[index]
        rows.append(
            f"""set_option maxRecDepth 100000 in
theorem {representative.lean_name}_generation_certificate :
    generatedStage (representative {index}) (representativeDepth {index}) =
      classElements (representativeClass {index}) := by
  decide
"""
        )
    return generated_header() + f"""import PolynomialFormulas.Fin5TransitiveClassificationGenerationCore

namespace {NAMESPACE}

{"\n".join(rows)}
end {NAMESPACE}
"""


def render_symmetric_structural_step(
    index: int,
    camel_name: str,
    depth: int,
    source_name: str,
    target_name: str,
) -> str:
    """Render a large S5 step from small membership and inverse witnesses."""
    representative = REPRESENTATIVES[index]
    source = generated_stage(representative.images, depth)
    target = generated_stage(representative.images, depth + 1)
    buckets = structural_step_additions(representative.images, source, target)
    letter_expressions = (
        "fiveCycle",
        "fiveCycle⁻¹",
        f"representative {index}",
        f"(representative {index})⁻¹",
    )
    letter_labels = ("rotation", "rotationInv", "generator", "generatorInv")
    option_line = "set_option maxRecDepth 100000 in"
    prefix = f"{camel_name}_step_{depth}"

    added_definitions = []
    added_names: dict[int, str] = {}
    for letter_index, bucket in enumerate(buckets):
        if not bucket:
            continue
        added_name = f"{camel_name}Step{depth}Added{letter_index}"
        codes_name = f"{added_name}Codes"
        added_names[letter_index] = added_name
        bucket_codes = sorted(permutation_code(element) for element in bucket)
        added_definitions.append(
            render_code_finset_definition(codes_name, bucket_codes)
            + f"""
def {added_name} : Finset S5 :=
  elementsWithCodes {codes_name}
"""
        )

    source_subset_name = f"{prefix}_source_subset_certificate"
    computational_certificates = [
        f"""{option_line}
theorem {source_subset_name} :
    ∀ x : S5, x ∈ {source_name} → x ∈ {target_name} := by
  decide
"""
    ]
    closure_names = []
    for letter_expression, letter_label in zip(
        letter_expressions, letter_labels, strict=True
    ):
        closure_name = f"{prefix}_{letter_label}_closed_certificate"
        closure_names.append(closure_name)
        computational_certificates.append(
            f"""{option_line}
theorem {closure_name} :
    ∀ x : S5, x ∈ {source_name} →
      {letter_expression} * x ∈ {target_name} := by
  decide
"""
        )

    lower_cases_name = f"{prefix}_lower_cases_certificate"
    lower_memberships = [f"x ∈ {source_name}"] + [
        f"x ∈ {added_names[letter_index]}" for letter_index in added_names
    ]
    lower_disjunction = " ∨\n        ".join(lower_memberships)
    computational_certificates.append(
        f"""{option_line}
theorem {lower_cases_name} :
    ∀ x : S5, x ∈ {target_name} →
      {lower_disjunction} := by
  decide
"""
    )

    preimage_names: dict[int, str] = {}
    for letter_index, added_name in added_names.items():
        preimage_name = f"{prefix}_added_{letter_index}_preimage_certificate"
        preimage_names[letter_index] = preimage_name
        letter_expression = letter_expressions[letter_index]
        computational_certificates.append(
            f"""{option_line}
theorem {preimage_name} :
    ∀ x : S5, x ∈ {added_name} →
      ({letter_expression})⁻¹ * x ∈ {source_name} := by
  decide
"""
        )

    upper_hypotheses = (
        "hsource",
        "hrotation",
        "hrotationInv",
        "hgenerator",
        "hgeneratorInv",
    )
    upper_branches = [
        f"    · exact {source_subset_name} x hsource"
    ]
    for hypothesis, closure_name in zip(
        upper_hypotheses[1:], closure_names, strict=True
    ):
        upper_branches.append(
            f"""    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp {hypothesis}
      exact {closure_name} y hy"""
        )

    lower_hypotheses = ["hsource"] + [
        f"hadded{letter_index}" for letter_index in added_names
    ]
    lower_branches = ["    · simp [generationStep, hsource]"]
    image_injections = (
        "Or.inl (Or.inl (Or.inl (Or.inr himage)))",
        "Or.inl (Or.inl (Or.inr himage))",
        "Or.inl (Or.inr himage)",
        "Or.inr himage",
    )
    for letter_index, added_name in added_names.items():
        letter_expression = letter_expressions[letter_index]
        hypothesis = f"hadded{letter_index}"
        lower_branches.append(
            f"""    · have hpre := {preimage_names[letter_index]} x {hypothesis}
      have himage :
          x ∈ {source_name}.image (fun y ↦ {letter_expression} * y) := by
        apply Finset.mem_image.mpr
        exact ⟨({letter_expression})⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact {image_injections[letter_index]}"""
        )

    theorem_name = f"{camel_name}_step_{depth}_certificate"
    return "\n".join(added_definitions) + "\n" + "\n".join(
        computational_certificates
    ) + f"""

/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem {theorem_name} :
    generationStep (representative {index}) {source_name} =
      {target_name} := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
{chr(10).join(upper_branches)}
  · intro x hx
    have hcases := {lower_cases_name} x hx
    rcases hcases with {" | ".join(lower_hypotheses)}
{chr(10).join(lower_branches)}
"""


def render_checkpoint_generation(index: int) -> str:
    representative = REPRESENTATIVES[index]
    if representative.checkpoint_depth is None:
        raise RuntimeError(f"row {index} has no checkpoint")
    checkpoint_depth = representative.checkpoint_depth
    remaining_depth = representative.depth - checkpoint_depth
    checkpoint = generated_stage(representative.images, checkpoint_depth)
    codes = sorted(permutation_code(permutation) for permutation in checkpoint)
    camel_name = representative.lean_name[0].lower() + representative.lean_name[1:]
    module_import = "PolynomialFormulas.Fin5TransitiveClassificationGenerationCore"
    def render_stage_definition(stage_name: str, stage_codes: list[int]) -> str:
        return f"""def {stage_name}Codes : Finset ℕ :=
{render_nat_list(stage_codes)}.toFinset

def {stage_name} : Finset S5 :=
  elementsWithCodes {stage_name}Codes
"""

    is_symmetric = representative.class_name == "symmetric"
    checkpoint_name = f"{camel_name}Checkpoint"
    stage_names: dict[int, str] = {}
    stage_definitions = []
    if is_symmetric:
        stage_names[0] = f"{camel_name}Stage0"
        stage_definitions.append(
            f"def {stage_names[0]} : Finset S5 := {{1}}\n"
        )
        for depth in range(1, checkpoint_depth):
            stage_name = f"{camel_name}Stage{depth}"
            stage_names[depth] = stage_name
            stage_codes = sorted(
                permutation_code(permutation)
                for permutation in generated_stage(representative.images, depth)
            )
            stage_definitions.append(
                render_stage_definition(stage_name, stage_codes)
            )
    stage_names[checkpoint_depth] = checkpoint_name
    stage_definitions.append(render_stage_definition(checkpoint_name, codes))
    for depth in range(checkpoint_depth + 1, representative.depth):
        stage_name = f"{camel_name}Stage{depth}"
        stage_names[depth] = stage_name
        stage_codes = sorted(
            permutation_code(permutation)
            for permutation in generated_stage(representative.images, depth)
        )
        stage_definitions.append(
            render_stage_definition(stage_name, stage_codes)
        )

    checkpoint_step_certificates = []
    checkpoint_step_names = []
    finish_step_certificates = []
    finish_step_names = []
    step_option_lines = "set_option maxRecDepth 100000 in"
    first_step_depth = 0 if is_symmetric else checkpoint_depth
    for depth in range(first_step_depth, representative.depth):
        theorem_name = f"{camel_name}_step_{depth}_certificate"
        source = stage_names[depth]
        if depth + 1 < representative.depth:
            target = stage_names[depth + 1]
        else:
            target = f"classElements (representativeClass {index})"
        if is_symmetric:
            rendered_step = render_symmetric_structural_step(
                index, camel_name, depth, source, target
            )
        else:
            rendered_step = f"""{step_option_lines}
theorem {theorem_name} :
    generationStep (representative {index}) {source} =
      {target} := by
  decide
"""
        if depth < checkpoint_depth:
            checkpoint_step_certificates.append(rendered_step)
            checkpoint_step_names.append(theorem_name)
        else:
            finish_step_certificates.append(rendered_step)
            finish_step_names.append(theorem_name)

    if is_symmetric:
        checkpoint_expression = stage_names[0]
        for _ in range(checkpoint_depth):
            checkpoint_expression = (
                f"generationStep (representative {index}) "
                f"({checkpoint_expression})"
            )
        checkpoint_proof = f"""theorem {camel_name}_checkpoint_certificate :
    generatedStage (representative {index}) {checkpoint_depth} =
      {checkpoint_name} := by
  change {checkpoint_expression} = {checkpoint_name}
  rw [{", ".join(checkpoint_step_names)}]
"""
    else:
        checkpoint_proof = f"""set_option maxRecDepth 100000 in
theorem {camel_name}_checkpoint_certificate :
    generatedStage (representative {index}) {checkpoint_depth} =
      {checkpoint_name} := by
  decide
"""

    finish_expression = f"{camel_name}Checkpoint"
    for _ in range(remaining_depth):
        finish_expression = (
            f"generationStep (representative {index}) ({finish_expression})"
        )
    return generated_header() + f"""import {module_import}

namespace {NAMESPACE}

{"\n".join(stage_definitions)}

{"\n".join(checkpoint_step_certificates)}

{checkpoint_proof}

{"\n".join(finish_step_certificates)}

theorem {camel_name}_finish_certificate :
    iterateGenerationStep (representative {index})
      {camel_name}Checkpoint {remaining_depth} =
        classElements (representativeClass {index}) := by
  change {finish_expression} = classElements (representativeClass {index})
  rw [{", ".join(finish_step_names)}]

theorem {camel_name}_generation_certificate :
    generatedStage (representative {index}) (representativeDepth {index}) =
      classElements (representativeClass {index}) := by
  change generatedStage (representative {index}) {representative.depth} =
    classElements (representativeClass {index})
  calc
    generatedStage (representative {index}) {representative.depth} =
        iterateGenerationStep (representative {index})
          (generatedStage (representative {index}) {checkpoint_depth})
          {remaining_depth} := by
      simpa using generatedStage_add (representative {index})
        {checkpoint_depth} {remaining_depth}
    _ = iterateGenerationStep (representative {index})
          {camel_name}Checkpoint {remaining_depth} := by
      rw [{camel_name}_checkpoint_certificate]
    _ = classElements (representativeClass {index}) :=
      {camel_name}_finish_certificate

end {NAMESPACE}
"""


def render_certificate_aggregate() -> str:
    return generated_header() + f"""import PolynomialFormulas.Fin5TransitiveClassificationDoubleCosetCertificate
import PolynomialFormulas.Fin5TransitiveClassificationAffineGenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationAlternating0GenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationAlternating1GenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationSymmetric0GenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationSymmetric1GenerationCertificate
import Mathlib.Tactic

namespace {NAMESPACE}

/-- Bounded replacement for the old 120-step all-generators computation. -/
theorem representative_generation_certificate (i : Fin 8) :
    generatedStage (representative i) (representativeDepth i) =
      classElements (representativeClass i) := by
  fin_cases i
  · exact cyclic_generation_certificate
  · exact dihedral_generation_certificate
  · exact frobenius0_generation_certificate
  · exact frobenius1_generation_certificate
  · exact alternating0_generation_certificate
  · exact alternating1_generation_certificate
  · exact symmetric0_generation_certificate
  · exact symmetric1_generation_certificate

theorem classElements_le_of_standardC5_le
    (H : Subgroup S5) (g : S5)
    (hC : standardC5 ≤ H) (hg : g ∈ H) :
    ∀ x : S5, x ∈ classElements (elementClass g) → x ∈ H := by
  obtain ⟨i, a, b, hdecomp, hclass⟩ :=
    exists_rotation_decomposition g
  have hrep : representative i ∈ H := by
    have hleft : fiveCycle ^ (a : ℕ) ∈ H :=
      Subgroup.pow_mem H (hC (Subgroup.mem_zpowers fiveCycle)) _
    have hright : fiveCycle ^ (b : ℕ) ∈ H :=
      Subgroup.pow_mem H (hC (Subgroup.mem_zpowers fiveCycle)) _
    have hcancel :
        (fiveCycle ^ (a : ℕ))⁻¹ * g *
            (fiveCycle ^ (b : ℕ))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hleft) hg) (H.inv_mem hright)
    rw [hdecomp] at hcancel
    simpa [mul_assoc] using hcancel
  intro x hx
  rw [hclass] at hx
  rw [← representative_generation_certificate i] at hx
  exact generatedStage_subset_subgroup H (representative i)
    (hC (Subgroup.mem_zpowers fiveCycle)) hrep
    (representativeDepth i) x hx

end {NAMESPACE}
"""


def render_outputs() -> dict[str, str]:
    validate_model()
    return {
        "Fin5TransitiveClassificationCertificateData.lean": render_data_module(),
        "Fin5TransitiveClassificationGenerationCore.lean": render_generation_core(),
        "Fin5TransitiveClassificationEvenCoverCertificate.lean": render_even_cover(),
        "Fin5TransitiveClassificationOddCoverCertificate.lean": render_odd_cover(),
        "Fin5TransitiveClassificationDoubleCosetCertificate.lean": (
            render_double_coset_aggregate()
        ),
        "Fin5TransitiveClassificationAffineGenerationCertificate.lean": (
            render_affine_generation()
        ),
        "Fin5TransitiveClassificationAlternating0GenerationCertificate.lean": (
            render_checkpoint_generation(4)
        ),
        "Fin5TransitiveClassificationAlternating1GenerationCertificate.lean": (
            render_checkpoint_generation(5)
        ),
        "Fin5TransitiveClassificationSymmetric0GenerationCertificate.lean": (
            render_checkpoint_generation(6)
        ),
        "Fin5TransitiveClassificationSymmetric1GenerationCertificate.lean": (
            render_checkpoint_generation(7)
        ),
        "Fin5TransitiveClassificationCertificates.lean": (
            render_certificate_aggregate()
        ),
    }


def check_outputs(outputs: dict[str, str]) -> bool:
    clean = True
    for filename, expected in outputs.items():
        path = LEAN_DIR / filename
        if not path.exists():
            print(f"missing: {path.relative_to(ROOT)}", file=sys.stderr)
            clean = False
            continue
        actual = path.read_text(encoding="utf-8")
        if actual != expected:
            print(f"stale: {path.relative_to(ROOT)}", file=sys.stderr)
            clean = False
    return clean


def write_outputs(outputs: dict[str, str]) -> None:
    for filename, source in outputs.items():
        path = LEAN_DIR / filename
        if path.exists() and path.read_text(encoding="utf-8") == source:
            continue
        path.write_text(source, encoding="utf-8")
        print(f"wrote {path.relative_to(ROOT)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate the model and fail if any generated file differs",
    )
    args = parser.parse_args()
    outputs = render_outputs()
    if args.check:
        if not check_outputs(outputs):
            return 1
        print(f"validated 8 representatives and {len(outputs)} generated Lean modules")
        return 0
    write_outputs(outputs)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
