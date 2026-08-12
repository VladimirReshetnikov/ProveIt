#!/usr/bin/env python3
"""Generate bounded, kernel-checked certificates for Dummit's large rows.

The first four coefficient identities in ``ComputableDummitCoefficients``
are too large for one kernel reduction.  This generator performs the sparse
integer arithmetic independently, emits small Lean data shards, and emits
ordinary ``decide`` proofs which Lean's kernel checks.  No generated theorem
trusts the Python computation: every normal form is compared with its Lean
source expression inside Lean.
"""

from __future__ import annotations

import argparse
import re
from collections import defaultdict
from itertools import combinations
from pathlib import Path


Exponent = tuple[int, int, int, int, int]
Polynomial = dict[Exponent, int]
Term = tuple[int, Exponent]
TermList = list[Term]

ZERO: Exponent = (0, 0, 0, 0, 0)
ROOT = Path(__file__).resolve().parents[3]
LEAN_DIR = ROOT / "Algebra/PolynomialFormulas/Lean/PolynomialFormulas"
SOURCE = LEAN_DIR / "ComputableDummitCoefficientsCore.lean"
if not SOURCE.exists():
    SOURCE = LEAN_DIR / "ComputableDummitCoefficients.lean"
PREFIX = "ComputableDummitKernelCertificate"
NAMESPACE = (
    "LeanProofs.PolynomialFormulas.ComputableDummitCoefficients."
    "KernelCertificate"
)
TABLE_BLOCK_SIZE = 4
# A direct certificate unfolds the whole accumulator chain at once.  Shard
# either a single large multiplication or a long sequence whose cumulative
# normalization work is large.  The second guard is needed for terms such as
# table 0, term 131: no individual multiplication crosses the peak threshold,
# but checking all eight multiplications in one reduction uses excessive
# memory.
TERM_STATE_SHARD_THRESHOLD = 30000
# A single accumulator multiplication can still retain the raw product and
# all five radix-sort intermediates while reducing `normalize`.  Above this
# raw row count, expose those normalization stages as separate certificates.
TERM_NORMALIZE_SHARD_THRESHOLD = 10000
RAW_MUL_LEFT_CHUNK_SIZE = 100
# Keep `flattenBuckets` certificates at one stable radix bucket apiece.  This
# avoids comparing the complete raw-product list with its flattened copy in a
# single kernel reduction, while retaining the exact bucket and term order.
FLATTEN_BUCKET_CHUNK_SIZE = 1
TERM_STATE_SHARD_TOTAL_THRESHOLD = 40000
# This term sits just below the generic cumulative-work threshold, but its
# long e₃ accumulator chain has empirically exceeded the available memory as
# one reduction.  Keep the exception explicit and target-scoped: lowering the
# global threshold would needlessly shard several already-tractable terms.
FORCE_SHARDED_TABLE_TERMS = {(0, 51), (0, 125)}


def add(*polynomials: Polynomial) -> Polynomial:
    result: defaultdict[Exponent, int] = defaultdict(int)
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] += coefficient
    return {exponent: coefficient for exponent, coefficient in result.items()
            if coefficient}


def scale(coefficient: int, polynomial: Polynomial) -> Polynomial:
    return {exponent: coefficient * value
            for exponent, value in polynomial.items()
            if coefficient * value}


def mul(*polynomials: Polynomial) -> Polynomial:
    result: Polynomial = {ZERO: 1}
    for polynomial in polynomials:
        next_result: defaultdict[Exponent, int] = defaultdict(int)
        for left_exponent, left_coefficient in result.items():
            for right_exponent, right_coefficient in polynomial.items():
                exponent = tuple(a + b for a, b in
                                 zip(left_exponent, right_exponent))
                next_result[exponent] += left_coefficient * right_coefficient
        result = {exponent: coefficient
                  for exponent, coefficient in next_result.items()
                  if coefficient}
    return result


def power(polynomial: Polynomial, exponent: int) -> Polynomial:
    result = {ZERO: 1}
    base = polynomial
    while exponent:
        if exponent & 1:
            result = mul(result, base)
        exponent //= 2
        if exponent:
            base = mul(base, base)
    return result


def variable(index: int) -> Polynomial:
    exponent = [0, 0, 0, 0, 0]
    exponent[index] = 1
    return {tuple(exponent): 1}


VARIABLES = [variable(index) for index in range(5)]
ELEMENTARY = [
    add(*(mul(*[VARIABLES[index] for index in subset])
          for subset in combinations(range(5), degree)))
    for degree in range(1, 6)
]


def substitute_term(term: Term) -> Polynomial:
    coefficient, exponents = term
    result = {ZERO: coefficient}
    for polynomial, exponent in zip(ELEMENTARY, exponents):
        result = mul(result, power(polynomial, exponent))
    return result


def substitute_term_accum(term: Term) -> Polynomial:
    """Mirror Lean's factor-at-a-time implementation independently."""
    coefficient, exponents = term
    result = {ZERO: coefficient}
    for polynomial, exponent in zip(ELEMENTARY, exponents):
        for _ in range(exponent):
            result = mul(result, polynomial)
    return result


def substitute_term_accum_trace(term: Term) -> tuple[list[Polynomial], list[int]]:
    """Every normalized state and factor index in Lean's accumulator.

    ``states[0]`` is the normalized constant and ``states[n + 1]`` is the
    result of multiplying ``states[n]`` by ``ELEMENTARY[factors[n]]``.
    Keeping this trace explicit lets Lean check each normalization separately
    and lets the final source theorem compose those small kernel equalities.
    """
    coefficient, exponents = term
    result = {ZERO: coefficient}
    states = [result]
    factors: list[int] = []
    for index, (polynomial, exponent) in enumerate(zip(ELEMENTARY, exponents)):
        for _ in range(exponent):
            result = mul(result, polynomial)
            states.append(result)
            factors.append(index)
    return states, factors


def polynomial_terms(polynomial: Polynomial) -> TermList:
    """The exact canonical list emitted for a normalized polynomial."""
    return [(coefficient, exponent)
            for exponent, coefficient in sorted(polynomial.items())]


def raw_mul_terms(left: Polynomial, right: Polynomial) -> TermList:
    """Mirror `SparsePolynomial.rawMul` on canonical source lists."""
    return raw_mul_term_lists(polynomial_terms(left), polynomial_terms(right))


def raw_mul_term_lists(left: TermList, right: TermList) -> TermList:
    """Mirror `SparsePolynomial.rawMul` on two explicit source lists."""
    result: TermList = []
    for left_coefficient, left_exponent in left:
        for right_coefficient, right_exponent in right:
            result.append((
                left_coefficient * right_coefficient,
                tuple(a + b for a, b in
                      zip(left_exponent, right_exponent)),
            ))
    return result


def radix_pass_terms(terms: TermList, coordinate: int) -> TermList:
    """Mirror the stable bucket/radix pass at one powers coordinate."""
    return sorted(terms, key=lambda term: term[1][coordinate])


def bucketize_terms(terms: TermList, coordinate: int) -> list[TermList]:
    """Mirror `bucketize` as stable ascending finite buckets."""
    buckets: list[TermList] = []
    for term in terms:
        key = term[1][coordinate]
        while len(buckets) <= key:
            buckets.append([])
        buckets[key].append(term)
    return buckets


def combine_terms(terms: TermList) -> Polynomial:
    """Mirror `SparsePolynomial.combine` on an already sorted list."""
    result: Polynomial = {}
    for coefficient, exponent in terms:
        result[exponent] = result.get(exponent, 0) + coefficient
        if result[exponent] == 0:
            del result[exponent]
    return result


def lean_substitute_cost(term: Term) -> tuple[int, int]:
    """Maximum raw multiplication rows and total rows in Lean's accumulator."""
    coefficient, exponents = term
    result: Polynomial = {ZERO: coefficient}
    costs: list[int] = []
    for polynomial, exponent in zip(ELEMENTARY, exponents):
        for _ in range(exponent):
            costs.append(len(result) * len(polynomial))
            result = mul(result, polynomial)
    return max(costs, default=0), sum(costs)


def find_matching_bracket(source: str, start: int) -> int:
    depth = 0
    for index in range(start, len(source)):
        if source[index] == "[":
            depth += 1
        elif source[index] == "]":
            depth -= 1
            if depth == 0:
                return index
    raise ValueError("unbalanced list literal")


TERM_RE = re.compile(
    r"⟨\s*(-?\d+)\s*,\s*⟨\s*(\d+)\s*,\s*(\d+)\s*,\s*"
    r"(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*⟩\s*⟩"
)


def parse_table() -> list[list[Term]]:
    source = SOURCE.read_text()
    marker = "def dummitTable : Fin 7 → SparsePolynomial :="
    start = source.index("![", source.index(marker)) + 1
    end = find_matching_bracket(source, start)
    body = source[start + 1:end]
    rows: list[list[Term]] = []
    index = 0
    while len(rows) < 7:
        row_start = body.index("[", index)
        row_end = find_matching_bracket(body, row_start)
        row_source = body[row_start + 1:row_end]
        row = [
            (int(match.group(1)), tuple(map(int, match.groups()[1:])))
            for match in TERM_RE.finditer(row_source)
        ]
        rows.append(row)
        index = row_end + 1
    return rows


# Permutations are written as their action on a variable index.  These are
# id, (012), (021), (01), (12), (02), matching Fin5TransitiveC5.representative.
REPRESENTATIVES = [
    (0, 1, 2, 3, 4),
    (1, 2, 0, 3, 4),
    (2, 0, 1, 3, 4),
    (1, 0, 2, 3, 4),
    (0, 2, 1, 3, 4),
    (2, 1, 0, 3, 4),
]


THETA_TERMS = [
    (0, 1, 4), (0, 2, 3), (1, 0, 2), (1, 3, 4), (2, 0, 4),
    (2, 1, 3), (3, 0, 1), (3, 2, 4), (4, 0, 3), (4, 1, 2),
]


def theta_polynomial(permutation: tuple[int, ...]) -> Polynomial:
    result: Polynomial = {}
    for squared, first, second in THETA_TERMS:
        exponent = [0, 0, 0, 0, 0]
        exponent[permutation[squared]] += 2
        exponent[permutation[first]] += 1
        exponent[permutation[second]] += 1
        result = add(result, {tuple(exponent): 1})
    return result


THETAS = [theta_polynomial(permutation)
          for permutation in REPRESENTATIVES]


def root_coefficient(index: int) -> Polynomial:
    degree = 6 - index
    sign = -1 if degree % 2 else 1
    return scale(sign, add(*(
        mul(*[THETAS[i] for i in subset])
        for subset in combinations(range(6), degree)
    )))


def esymm_state(start: int, degree: int,
                 cache: dict[tuple[int, int], Polynomial] | None = None
                 ) -> Polynomial:
    if cache is None:
        cache = {}
    key = (start, degree)
    if key in cache:
        return cache[key]
    if degree == 0:
        result = {ZERO: 1}
    elif start == len(THETAS):
        result = {}
    else:
        result = add(esymm_state(start + 1, degree, cache),
                     mul(THETAS[start],
                         esymm_state(start + 1, degree - 1, cache)))
    cache[key] = result
    return result


def table_coefficient(row: list[Term]) -> Polynomial:
    return add(*(substitute_term(term) for term in row))


def lean_polynomial(name: str, polynomial: Polynomial) -> str:
    return lean_term_list(name, polynomial_terms(polynomial))


def lean_term_list(name: str, terms: TermList) -> str:
    lines = [f"def {name} : SparsePolynomial := ["]
    for position, (coefficient, exponent) in enumerate(terms):
        comma = "," if position + 1 < len(terms) else ""
        powers = ", ".join(str(value) for value in exponent)
        lines.append(f"  ⟨{coefficient}, ⟨{powers}⟩⟩{comma}")
    lines.append("]")
    return "\n".join(lines)


def lean_bucket_list(name: str, buckets: list[TermList]) -> str:
    lines = [f"def {name} : List SparsePolynomial := ["]
    for bucket_position, bucket in enumerate(buckets):
        bucket_comma = "," if bucket_position + 1 < len(buckets) else ""
        if not bucket:
            lines.append(f"  []{bucket_comma}")
            continue
        lines.append("  [")
        for term_position, (coefficient, exponent) in enumerate(bucket):
            comma = "," if term_position + 1 < len(bucket) else ""
            powers = ", ".join(str(value) for value in exponent)
            lines.append(f"    ⟨{coefficient}, ⟨{powers}⟩⟩{comma}")
        lines.append(f"  ]{bucket_comma}")
    lines.append("]")
    return "\n".join(lines)


def lean_term(term: Term) -> str:
    coefficient, exponent = term
    powers = ", ".join(str(value) for value in exponent)
    return f"⟨{coefficient}, ⟨{powers}⟩⟩"


def module_text(imports: list[str], declarations: list[str]) -> str:
    return "\n\n".join([
        *(f"import PolynomialFormulas.{module}" for module in imports),
        f"namespace {NAMESPACE}",
        "open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 20000000",
        *declarations,
        f"end {NAMESPACE}",
    ]) + "\n"


WRITTEN_MODULES: set[str] = set()


def write_module(name: str, imports: list[str], declarations: list[str]) -> None:
    (LEAN_DIR / f"{name}.lean").write_text(module_text(imports, declarations))
    WRITTEN_MODULES.add(name)


def write_target_manifest_and_check(index: int, position: int) -> None:
    """Record and reject stale generated shards for one exact table term.

    This is deliberately non-destructive: the target-scoped manifest makes
    every generated source explicit, and an obsolete shard causes generation
    to fail with its exact filename instead of deleting through a broad glob.
    """
    target_prefix = f"{PREFIX}Table{index}Term{position}"
    expected = sorted(
        f"{module}.lean" for module in WRITTEN_MODULES
        if module.startswith(target_prefix)
    )
    manifest = LEAN_DIR / f"{target_prefix}GeneratedFiles.txt"
    manifest.write_text("\n".join(expected) + "\n")
    existing = {
        path.name for path in LEAN_DIR.glob(f"{target_prefix}*.lean")
    }
    unexpected = sorted(existing.difference(expected))
    missing = sorted(set(expected).difference(existing))
    if unexpected or missing:
        details = []
        if unexpected:
            details.append("stale generated shards: " + ", ".join(unexpected))
        if missing:
            details.append("missing generated shards: " + ", ".join(missing))
        raise RuntimeError("; ".join(details))


def decide_theorem(name: str, statement: str, depth: int = 1000000) -> str:
    return (f"set_option maxRecDepth {depth} in\n"
            "set_option maxHeartbeats 20000000 in\n"
            f"theorem {name} :\n    {statement} := by\n  decide")


def nested_add(expressions: list[str], tail: str) -> str:
    result = tail
    for expression in reversed(expressions):
        result = f"SparsePolynomial.add {expression} ({result})"
    return result


def table_word(index: int) -> str:
    return ["zero", "one", "two", "three"][index]


def table_term_data_module(index: int, position: int) -> str:
    return f"{PREFIX}Table{index}Term{position}Data"


def table_term_certificate_module(index: int, position: int) -> str:
    return f"{PREFIX}Table{index}Term{position}Certificate"


def table_term_normal(index: int, position: int) -> str:
    return f"table{index}Term{position}Normal"


def table_term_certificate(index: int, position: int) -> str:
    return f"table{index}_term{position}_certificate"


def table_term_state_data_module(index: int, position: int, state: int) -> str:
    return f"{PREFIX}Table{index}Term{position}State{state}Data"


def table_term_state_certificate_module(
        index: int, position: int, state: int) -> str:
    return f"{PREFIX}Table{index}Term{position}State{state}Certificate"


def table_term_state_normal(index: int, position: int, state: int) -> str:
    return f"table{index}Term{position}State{state}Normal"


def table_term_state_certificate(index: int, position: int, state: int) -> str:
    return f"table{index}_term{position}_state{state}_certificate"


def table_term_state_normalize_data_module(
        index: int, position: int, state: int, stage: str) -> str:
    return (f"{PREFIX}Table{index}Term{position}State{state}"
            f"Normalize{stage}Data")


def table_term_state_normalize_certificate_module(
        index: int, position: int, state: int, stage: str) -> str:
    return (f"{PREFIX}Table{index}Term{position}State{state}"
            f"Normalize{stage}Certificate")


def table_term_state_normalize_normal(
        index: int, position: int, state: int, stage: str) -> str:
    return f"table{index}Term{position}State{state}Normalize{stage}Normal"


def table_term_state_normalize_certificate(
        index: int, position: int, state: int, stage: str) -> str:
    return (f"table{index}_term{position}_state{state}_normalize_"
            f"{stage.lower()}_certificate")


def table_term_state_raw_left_data_module(
        index: int, position: int, state: int, chunk: int) -> str:
    return (f"{PREFIX}Table{index}Term{position}State{state}"
            f"NormalizeRawLeftChunk{chunk}Data")


def table_term_state_raw_left_normal(
        index: int, position: int, state: int, chunk: int) -> str:
    return (f"table{index}Term{position}State{state}"
            f"NormalizeRawLeftChunk{chunk}Normal")


def table_term_state_raw_chunk_data_module(
        index: int, position: int, state: int, chunk: int) -> str:
    return (f"{PREFIX}Table{index}Term{position}State{state}"
            f"NormalizeRawChunk{chunk}Data")


def table_term_state_raw_chunk_normal(
        index: int, position: int, state: int, chunk: int) -> str:
    return (f"table{index}Term{position}State{state}"
            f"NormalizeRawChunk{chunk}Normal")


def table_term_state_raw_chunk_certificate_module(
        index: int, position: int, state: int, chunk: int) -> str:
    return (f"{PREFIX}Table{index}Term{position}State{state}"
            f"NormalizeRawChunk{chunk}Certificate")


def table_term_state_raw_chunk_certificate(
        index: int, position: int, state: int, chunk: int) -> str:
    return (f"table{index}_term{position}_state{state}_normalize_"
            f"raw_chunk{chunk}_certificate")


def table_term_state_flatten_chunk_data_module(
        index: int, position: int, state: int,
        coordinate: int, chunk: int) -> str:
    return (f"{PREFIX}Table{index}Term{position}State{state}"
            f"NormalizeRadix{coordinate}FlattenChunk{chunk}Data")


def table_term_state_flatten_chunk_bucket_normal(
        index: int, position: int, state: int,
        coordinate: int, bucket: int) -> str:
    return (f"table{index}Term{position}State{state}"
            f"NormalizeRadix{coordinate}Bucket{bucket}Normal")


def table_term_state_flatten_chunk_buckets_normal(
        index: int, position: int, state: int,
        coordinate: int, chunk: int) -> str:
    return (f"table{index}Term{position}State{state}"
            f"NormalizeRadix{coordinate}FlattenChunk{chunk}BucketsNormal")


def table_term_state_flatten_chunk_normal(
        index: int, position: int, state: int,
        coordinate: int, chunk: int) -> str:
    return (f"table{index}Term{position}State{state}"
            f"NormalizeRadix{coordinate}FlattenChunk{chunk}Normal")


def table_term_state_flatten_chunk_certificate_module(
        index: int, position: int, state: int,
        coordinate: int, chunk: int) -> str:
    return (f"{PREFIX}Table{index}Term{position}State{state}"
            f"NormalizeRadix{coordinate}FlattenChunk{chunk}Certificate")


def table_term_state_flatten_chunk_certificate(
        index: int, position: int, state: int,
        coordinate: int, chunk: int) -> str:
    return (f"table{index}_term{position}_state{state}_normalize_"
            f"radix{coordinate}_flatten_chunk{chunk}_certificate")


def nested_append(expressions: list[str]) -> str:
    assert expressions
    result = expressions[-1]
    for expression in reversed(expressions[:-1]):
        result = f"({expression} ++ {result})"
    return result


def table_tail_data_module(index: int, group: int) -> str:
    return f"{PREFIX}Table{index}Tail{group}Data"


def table_tail_certificate_module(index: int, group: int) -> str:
    return f"{PREFIX}Table{index}Tail{group}Certificate"


def table_tail_normal(index: int, group: int) -> str:
    return f"table{index}Tail{group}Normal"


def table_tail_certificate(index: int, group: int) -> str:
    return f"table{index}_tail{group}_certificate"


RAW_MUL_APPEND_MODULE = f"{PREFIX}RawMulAppend"
RAW_MUL_APPEND_CERTIFICATE = "rawMul_append_certificate"
FLATTEN_BUCKETS_APPEND_MODULE = f"{PREFIX}FlattenBucketsAppend"
FLATTEN_BUCKETS_APPEND_CERTIFICATE = "flattenBuckets_append_certificate"


def write_raw_mul_append_certificate() -> None:
    write_module(
        RAW_MUL_APPEND_MODULE,
        ["ComputableDummitCoefficientsCore"],
        [f"theorem {RAW_MUL_APPEND_CERTIFICATE} "
         "(p r q : SparsePolynomial) :\n"
         "    SparsePolynomial.rawMul (p ++ r) q =\n"
         "      SparsePolynomial.rawMul p q ++ "
         "SparsePolynomial.rawMul r q := by\n"
         "  induction p with\n"
         "  | nil => rfl\n"
         "  | cons t p ih =>\n"
         "      change q.map (SparseTerm.mul t) ++\n"
         "          SparsePolynomial.rawMul (p ++ r) q =\n"
         "        (q.map (SparseTerm.mul t) ++ "
         "SparsePolynomial.rawMul p q) ++\n"
         "          SparsePolynomial.rawMul r q\n"
         "      rw [ih, List.append_assoc]"])


def write_flatten_buckets_append_certificate() -> None:
    write_module(
        FLATTEN_BUCKETS_APPEND_MODULE,
        ["ComputableDummitCoefficientsCore"],
        [f"theorem {FLATTEN_BUCKETS_APPEND_CERTIFICATE} "
         "(p r : List SparsePolynomial) :\n"
         "    SparsePolynomial.flattenBuckets (p ++ r) =\n"
         "      SparsePolynomial.flattenBuckets p ++\n"
         "        SparsePolynomial.flattenBuckets r := by\n"
         "  induction p with\n"
         "  | nil => rfl\n"
         "  | cons b p ih =>\n"
         "      change b ++ SparsePolynomial.flattenBuckets (p ++ r) =\n"
         "        (b ++ SparsePolynomial.flattenBuckets p) ++\n"
         "          SparsePolynomial.flattenBuckets r\n"
         "      rw [ih, List.append_assoc]"])


def write_normalization_sharded_state_certificate(
        index: int, position: int, state: int, factor: int,
        previous_polynomial: Polynomial, current_polynomial: Polynomial,
        previous_data: str, current_data: str,
        previous_normal: str, current_normal: str) -> None:
    """Check one large `mul` one normalization pass at a time.

    A direct `decide` unfolds `rawMul`, all five stable radix passes, and
    `combine` in one reduction.  Materializing each pass independently keeps
    the kernel proof ordinary while bounding the live reduction graph.
    """
    write_raw_mul_append_certificate()
    write_flatten_buckets_append_certificate()
    left_terms = polynomial_terms(previous_polynomial)
    right_terms = polynomial_terms(ELEMENTARY[factor])
    left_chunks = [
        left_terms[start:start + RAW_MUL_LEFT_CHUNK_SIZE]
        for start in range(0, len(left_terms), RAW_MUL_LEFT_CHUNK_SIZE)
    ]
    raw_chunks = [raw_mul_term_lists(chunk, right_terms)
                  for chunk in left_chunks]
    raw_terms = [term for chunk in raw_chunks for term in chunk]
    assert raw_terms == raw_mul_terms(
        previous_polynomial, ELEMENTARY[factor])
    radix_stages: list[tuple[int, list[TermList], TermList]] = []
    terms = raw_terms
    for coordinate in reversed(range(5)):
        buckets = bucketize_terms(terms, coordinate)
        flattened = [term for bucket in buckets for term in bucket]
        assert flattened == radix_pass_terms(terms, coordinate)
        radix_stages.append((coordinate, buckets, flattened))
        terms = flattened
    assert combine_terms(terms) == current_polynomial

    left_normals = [
        table_term_state_raw_left_normal(index, position, state, chunk)
        for chunk in range(len(left_chunks))
    ]
    raw_chunk_normals = [
        table_term_state_raw_chunk_normal(index, position, state, chunk)
        for chunk in range(len(raw_chunks))
    ]
    raw_chunk_modules: list[str] = []
    raw_chunk_certificates: list[str] = []
    for chunk, (left_chunk, raw_chunk) in enumerate(
            zip(left_chunks, raw_chunks)):
        left_data = table_term_state_raw_left_data_module(
            index, position, state, chunk)
        raw_chunk_data = table_term_state_raw_chunk_data_module(
            index, position, state, chunk)
        write_module(
            left_data,
            ["ComputableDummitCoefficientsCore"],
            [lean_term_list(left_normals[chunk], left_chunk)])
        write_module(
            raw_chunk_data,
            ["ComputableDummitCoefficientsCore"],
            [lean_term_list(raw_chunk_normals[chunk], raw_chunk)])
        chunk_module = table_term_state_raw_chunk_certificate_module(
            index, position, state, chunk)
        chunk_certificate = table_term_state_raw_chunk_certificate(
            index, position, state, chunk)
        write_module(
            chunk_module,
            [left_data, raw_chunk_data],
            [decide_theorem(
                chunk_certificate,
                f"SparsePolynomial.rawMul {left_normals[chunk]} "
                f"(elementaryPolynomials {factor}) = "
                f"{raw_chunk_normals[chunk]}")])
        raw_chunk_modules.append(chunk_module)
        raw_chunk_certificates.append(chunk_certificate)

    raw_stage_data = table_term_state_normalize_data_module(
        index, position, state, "Raw")
    raw_stage_normal = table_term_state_normalize_normal(
        index, position, state, "Raw")
    write_module(
        raw_stage_data,
        [table_term_state_raw_chunk_data_module(
            index, position, state, chunk)
         for chunk in range(len(raw_chunks))],
        [f"def {raw_stage_normal} : SparsePolynomial :=\n"
         f"  {nested_append(raw_chunk_normals)}"])

    flatten_chunks_by_coordinate: dict[
        int, list[tuple[str, str, str, str]]
    ] = {}
    for coordinate, buckets, stage_value in radix_stages:
        stage_name = f"Radix{coordinate}"
        bucket_groups = [
            buckets[start:start + FLATTEN_BUCKET_CHUNK_SIZE]
            for start in range(0, len(buckets), FLATTEN_BUCKET_CHUNK_SIZE)
        ]
        assert [bucket for group in bucket_groups for bucket in group] == buckets
        chunk_records: list[tuple[str, str, str, str]] = []
        flattened_chunks: list[TermList] = []
        bucket_offset = 0
        for chunk, bucket_group in enumerate(bucket_groups):
            chunk_data = table_term_state_flatten_chunk_data_module(
                index, position, state, coordinate, chunk)
            bucket_normals = [
                table_term_state_flatten_chunk_bucket_normal(
                    index, position, state, coordinate, bucket_offset + local)
                for local in range(len(bucket_group))
            ]
            chunk_buckets_normal = \
                table_term_state_flatten_chunk_buckets_normal(
                    index, position, state, coordinate, chunk)
            chunk_normal = table_term_state_flatten_chunk_normal(
                index, position, state, coordinate, chunk)
            declarations = [
                lean_term_list(bucket_normal, bucket)
                for bucket_normal, bucket in zip(bucket_normals, bucket_group)
            ]
            declarations.extend([
                f"def {chunk_buckets_normal} : List SparsePolynomial :=\n"
                f"  [{', '.join(bucket_normals)}]",
                f"def {chunk_normal} : SparsePolynomial :=\n"
                f"  {nested_append(bucket_normals)}",
            ])
            write_module(
                chunk_data,
                ["ComputableDummitCoefficientsCore"],
                declarations)
            flattened_chunk = [
                term for bucket in bucket_group for term in bucket
            ]
            assert flattened_chunk == [
                term for bucket_normal, bucket in
                zip(bucket_normals, bucket_group) for term in bucket
            ]
            flattened_chunks.append(flattened_chunk)
            chunk_records.append((
                chunk_data, chunk_buckets_normal, chunk_normal,
                table_term_state_flatten_chunk_certificate(
                    index, position, state, coordinate, chunk),
            ))
            bucket_offset += len(bucket_group)
        assert bucket_offset == len(buckets)
        assert [
            term for flattened_chunk in flattened_chunks
            for term in flattened_chunk
        ] == stage_value
        flatten_chunks_by_coordinate[coordinate] = chunk_records

        write_module(
            table_term_state_normalize_data_module(
                index, position, state, stage_name),
            [record[0] for record in chunk_records],
            [f"def {table_term_state_normalize_normal(index, position, state, stage_name)} "
             ": SparsePolynomial :=\n"
             f"  {nested_append([record[2] for record in chunk_records])}"])
        bucket_stage = f"Radix{coordinate}Buckets"
        write_module(
            table_term_state_normalize_data_module(
                index, position, state, bucket_stage),
            [record[0] for record in chunk_records],
            [f"def {table_term_state_normalize_normal(index, position, state, bucket_stage)} "
             ": List SparsePolynomial :=\n"
             f"  {nested_append([record[1] for record in chunk_records])}"])

    certificate_modules: list[str] = []
    certificates: list[str] = []

    left_split_module = table_term_state_normalize_certificate_module(
        index, position, state, "RawLeftSplit")
    left_split_certificate = table_term_state_normalize_certificate(
        index, position, state, "RawLeftSplit")
    write_module(
        left_split_module,
        [previous_data,
         *(table_term_state_raw_left_data_module(
             index, position, state, chunk)
           for chunk in range(len(left_chunks)))],
        [decide_theorem(
            left_split_certificate,
            f"{previous_normal} = {nested_append(left_normals)}")])

    raw_module = table_term_state_normalize_certificate_module(
        index, position, state, "Raw")
    raw_certificate = table_term_state_normalize_certificate(
        index, position, state, "Raw")
    append_rewrites = [RAW_MUL_APPEND_CERTIFICATE] * (len(left_chunks) - 1)
    write_module(
        raw_module,
        [raw_stage_data, left_split_module, RAW_MUL_APPEND_MODULE,
         *raw_chunk_modules],
        [f"theorem {raw_certificate} :\n"
         f"    SparsePolynomial.rawMul {previous_normal} "
         f"(elementaryPolynomials {factor}) = {raw_stage_normal} := by\n"
         f"  rw [{left_split_certificate}]\n"
         f"  change SparsePolynomial.rawMul {nested_append(left_normals)} "
         f"(elementaryPolynomials {factor}) = "
         f"{nested_append(raw_chunk_normals)}\n"
         f"  rw [{', '.join(append_rewrites + raw_chunk_certificates)}]"])
    certificate_modules.append(raw_module)
    certificates.append(raw_certificate)

    previous_stage = "Raw"
    for coordinate in reversed(range(5)):
        stage_name = f"Radix{coordinate}"
        bucket_stage = f"Radix{coordinate}Buckets"
        bucket_module = table_term_state_normalize_certificate_module(
            index, position, state, f"Radix{coordinate}Bucketize")
        bucket_certificate = table_term_state_normalize_certificate(
            index, position, state, f"Radix{coordinate}Bucketize")
        write_module(
            bucket_module,
            [table_term_state_normalize_data_module(
                index, position, state, bucket_stage),
             table_term_state_normalize_data_module(
                index, position, state, previous_stage)],
            [decide_theorem(
                bucket_certificate,
                "SparsePolynomial.bucketize "
                f"(fun t ↦ t.powers.p{coordinate}) "
                f"{table_term_state_normalize_normal(index, position, state, previous_stage)} = "
                f"{table_term_state_normalize_normal(index, position, state, bucket_stage)}")])

        flatten_module = table_term_state_normalize_certificate_module(
            index, position, state, f"Radix{coordinate}Flatten")
        flatten_certificate = table_term_state_normalize_certificate(
            index, position, state, f"Radix{coordinate}Flatten")
        chunk_records = flatten_chunks_by_coordinate[coordinate]
        flatten_chunk_modules: list[str] = []
        flatten_chunk_certificates: list[str] = []
        for chunk, (chunk_data, chunk_buckets_normal, chunk_normal,
                    chunk_certificate) in enumerate(chunk_records):
            chunk_module = \
                table_term_state_flatten_chunk_certificate_module(
                    index, position, state, coordinate, chunk)
            write_module(
                chunk_module,
                [chunk_data],
                [decide_theorem(
                    chunk_certificate,
                    "SparsePolynomial.flattenBuckets "
                    f"{chunk_buckets_normal} = {chunk_normal}")])
            flatten_chunk_modules.append(chunk_module)
            flatten_chunk_certificates.append(chunk_certificate)
        append_rewrites = [FLATTEN_BUCKETS_APPEND_CERTIFICATE] * \
            (len(chunk_records) - 1)
        write_module(
            flatten_module,
            [table_term_state_normalize_data_module(
                index, position, state, bucket_stage),
             table_term_state_normalize_data_module(
                index, position, state, stage_name),
             FLATTEN_BUCKETS_APPEND_MODULE,
             *flatten_chunk_modules],
            [f"theorem {flatten_certificate} :\n"
             "    SparsePolynomial.flattenBuckets "
             f"{table_term_state_normalize_normal(index, position, state, bucket_stage)} = "
             f"{table_term_state_normalize_normal(index, position, state, stage_name)} := by\n"
             "  change SparsePolynomial.flattenBuckets "
             f"{nested_append([record[1] for record in chunk_records])} =\n"
             f"    {nested_append([record[2] for record in chunk_records])}\n"
             f"  rw [{', '.join(append_rewrites + flatten_chunk_certificates)}]"])

        module = table_term_state_normalize_certificate_module(
            index, position, state, stage_name)
        certificate = table_term_state_normalize_certificate(
            index, position, state, stage_name)
        write_module(
            module,
            [bucket_module, flatten_module],
            [f"theorem {certificate} :\n"
             "    SparsePolynomial.radixPass "
             f"(fun t ↦ t.powers.p{coordinate}) "
             f"{table_term_state_normalize_normal(index, position, state, previous_stage)} = "
             f"{table_term_state_normalize_normal(index, position, state, stage_name)} := by\n"
             "  change SparsePolynomial.flattenBuckets\n"
             "    (SparsePolynomial.bucketize "
             f"(fun t ↦ t.powers.p{coordinate}) "
             f"{table_term_state_normalize_normal(index, position, state, previous_stage)}) = _\n"
             f"  rw [{bucket_certificate}, {flatten_certificate}]"])
        certificate_modules.append(module)
        certificates.append(certificate)
        previous_stage = stage_name

    combine_module = table_term_state_normalize_certificate_module(
        index, position, state, "Combine")
    combine_certificate = table_term_state_normalize_certificate(
        index, position, state, "Combine")
    write_module(
        combine_module,
        [current_data,
         table_term_state_normalize_data_module(
             index, position, state, previous_stage)],
        [decide_theorem(
            combine_certificate,
            "SparsePolynomial.combine "
            f"{table_term_state_normalize_normal(index, position, state, previous_stage)} = "
            f"{current_normal}")])
    certificate_modules.append(combine_module)
    certificates.append(combine_certificate)

    source = f"SparsePolynomial.rawMul {previous_normal} (elementaryPolynomials {factor})"
    for coordinate in reversed(range(5)):
        source = ("SparsePolynomial.radixPass "
                  f"(fun t ↦ t.powers.p{coordinate}) ({source})")
    source = f"SparsePolynomial.combine ({source})"
    write_module(
        table_term_state_certificate_module(index, position, state),
        certificate_modules,
        [f"theorem {table_term_state_certificate(index, position, state)} :\n"
         f"    SparsePolynomial.mul {previous_normal} "
         f"(elementaryPolynomials {factor}) = {current_normal} := by\n"
         f"  change {source} = {current_normal}\n"
         f"  rw [{', '.join(certificates)}]"])


def write_sharded_table_term_certificate(
        index: int, position: int, term: Term) -> None:
    """Check one substitution one accumulator multiplication at a time."""
    states, factors = substitute_term_accum_trace(term)
    final_normal = table_term_normal(index, position)
    assert states[-1] == substitute_term(term)

    # The final state is the existing public term normal.  Earlier states get
    # independent data modules so no module elaborates all literals at once.
    for state, polynomial in enumerate(states[:-1]):
        write_module(
            table_term_state_data_module(index, position, state),
            ["ComputableDummitCoefficientsCore"],
            [lean_polynomial(
                table_term_state_normal(index, position, state), polynomial)])

    state_certificates: list[str] = []
    state_zero_certificate = table_term_state_certificate(index, position, 0)
    write_module(
        table_term_state_certificate_module(index, position, 0),
        [table_term_state_data_module(index, position, 0)],
        [decide_theorem(
            state_zero_certificate,
            f"SparsePolynomial.const ({term[0]}) = "
            f"{table_term_state_normal(index, position, 0)}")])
    state_certificates.append(state_zero_certificate)

    for state, factor in enumerate(factors, start=1):
        previous_normal = table_term_state_normal(index, position, state - 1)
        if state + 1 == len(states):
            current_normal = final_normal
            current_data = table_term_data_module(index, position)
        else:
            current_normal = table_term_state_normal(index, position, state)
            current_data = table_term_state_data_module(index, position, state)
        certificate = table_term_state_certificate(index, position, state)
        previous_data = table_term_state_data_module(
            index, position, state - 1)
        if len(states[state - 1]) * len(ELEMENTARY[factor]) >= \
                TERM_NORMALIZE_SHARD_THRESHOLD:
            write_normalization_sharded_state_certificate(
                index, position, state, factor,
                states[state - 1], states[state],
                previous_data, current_data,
                previous_normal, current_normal)
        else:
            write_module(
                table_term_state_certificate_module(index, position, state),
                [current_data, previous_data],
                [decide_theorem(
                    certificate,
                    f"SparsePolynomial.mul {previous_normal} "
                    f"(elementaryPolynomials {factor}) = {current_normal}")])
        state_certificates.append(certificate)

    source = f"SparsePolynomial.const ({term[0]})"
    for factor in factors:
        source = (f"SparsePolynomial.mul ({source}) "
                  f"(elementaryPolynomials {factor})")
    write_module(
        table_term_certificate_module(index, position),
        [table_term_state_certificate_module(index, position, state)
         for state in range(len(states))],
        [f"theorem {table_term_certificate(index, position)} :\n"
         f"    SparseTerm.substitute {lean_term(term)} "
         f"elementaryPolynomials = {final_normal} := by\n"
         f"  change {source} = {final_normal}\n"
         f"  rw [{', '.join(state_certificates)}]"])


def write_table_term_certificate_files(
        index: int, position: int, term: Term,
        force_sharded: bool = False) -> None:
    normal_name = table_term_normal(index, position)
    data_module = table_term_data_module(index, position)
    write_module(data_module, ["ComputableDummitCoefficientsCore"], [
        lean_polynomial(normal_name, substitute_term(term)),
    ])
    peak_cost, total_cost = lean_substitute_cost(term)
    if (force_sharded or
            (index, position) in FORCE_SHARDED_TABLE_TERMS or
            peak_cost >= TERM_STATE_SHARD_THRESHOLD or
            total_cost >= TERM_STATE_SHARD_TOTAL_THRESHOLD):
        write_sharded_table_term_certificate(index, position, term)
    else:
        write_module(table_term_certificate_module(index, position),
                     [data_module], [
            decide_theorem(
                table_term_certificate(index, position),
                f"SparseTerm.substitute {lean_term(term)} "
                f"elementaryPolynomials = {normal_name}"),
        ])


def write_table_term_certificates(index: int, row: list[Term]) -> None:
    for position, term in enumerate(row):
        write_table_term_certificate_files(index, position, term)


def write_table_row_data(index: int, row: list[Term]) -> tuple[str, int]:
    module = f"{PREFIX}Table{index}RowData"
    groups = [row[start:start + TABLE_BLOCK_SIZE]
              for start in range(0, len(row), TABLE_BLOCK_SIZE)]
    declarations: list[str] = []
    for group, terms in enumerate(groups):
        body = ",\n  ".join(lean_term(term) for term in terms)
        declarations.append(
            f"def table{index}Block{group} : SparsePolynomial := [\n"
            f"  {body}\n]")
    declarations.append(
        f"def table{index}Tail{len(groups)} : SparsePolynomial := []")
    for group in reversed(range(len(groups))):
        declarations.append(
            f"def table{index}Tail{group} : SparsePolynomial :=\n"
            f"  table{index}Block{group} ++ table{index}Tail{group + 1}")
    write_module(module, ["ComputableDummitCoefficientsCore"], declarations)
    return module, len(groups)


def write_table_tail_certificates(index: int, row: list[Term],
                                  row_data: str, group_count: int) -> None:
    base_data = table_tail_data_module(index, group_count)
    base_certificate = table_tail_certificate_module(index, group_count)
    write_module(base_data, [row_data], [
        f"def {table_tail_normal(index, group_count)} : SparsePolynomial := []",
    ])
    write_module(base_certificate, [base_data], [
        f"theorem {table_tail_certificate(index, group_count)} :\n"
        f"    SparsePolynomial.substitute table{index}Tail{group_count} "
        f"elementaryPolynomials = {table_tail_normal(index, group_count)} := by\n"
        "  rfl",
    ])

    suffix: Polynomial = {}
    suffix_normals: dict[int, Polynomial] = {group_count: suffix}
    for group in reversed(range(group_count)):
        start = group * TABLE_BLOCK_SIZE
        terms = row[start:start + TABLE_BLOCK_SIZE]
        suffix = add(*(substitute_term(term) for term in terms), suffix)
        suffix_normals[group] = suffix

    for group in reversed(range(group_count)):
        start = group * TABLE_BLOCK_SIZE
        positions = list(range(start, min(start + TABLE_BLOCK_SIZE, len(row))))
        data_module = table_tail_data_module(index, group)
        certificate_module = table_tail_certificate_module(index, group)
        normal_name = table_tail_normal(index, group)
        next_normal = table_tail_normal(index, group + 1)
        candidate_name = f"table{index}Tail{group}Candidate"
        normal_terms = [table_term_normal(index, position)
                        for position in positions]
        candidate = nested_add(normal_terms, next_normal)
        imports = [row_data, table_tail_certificate_module(index, group + 1)]
        imports += [table_term_certificate_module(index, position)
                    for position in positions]
        write_module(data_module, imports, [
            lean_polynomial(normal_name, suffix_normals[group]),
            f"def {candidate_name} : SparsePolynomial :=\n  {candidate}",
        ])
        merge_name = f"table{index}_tail{group}_merge_certificate"
        source_terms = [
            f"(SparseTerm.substitute {lean_term(row[position])} "
            "elementaryPolynomials)"
            for position in positions
        ]
        changed = nested_add(
            source_terms,
            f"SparsePolynomial.substitute table{index}Tail{group + 1} "
            "elementaryPolynomials")
        rewrites = [table_term_certificate(index, position)
                    for position in positions]
        rewrites.append(table_tail_certificate(index, group + 1))
        write_module(certificate_module, [data_module], [
            decide_theorem(merge_name, f"{candidate_name} = {normal_name}"),
            f"theorem {table_tail_certificate(index, group)} :\n"
            f"    SparsePolynomial.substitute table{index}Tail{group} "
            f"elementaryPolynomials = {normal_name} := by\n"
            f"  change {changed} = {normal_name}\n"
            f"  rw [{', '.join(rewrites)}]\n"
            f"  exact {merge_name}",
        ])


def write_table_final(index: int, row: list[Term], row_data: str) -> str:
    module = f"{PREFIX}Table{index}Final"
    word = table_word(index)
    row_certificate = f"dummitTable_{word}_source_certificate"
    final_certificate = f"tableInRoots_{word}_certificate"
    write_module(module, [row_data, table_tail_certificate_module(index, 0)], [
        decide_theorem(row_certificate,
            f"dummitTable {index} = table{index}Tail0", depth=100000),
        f"theorem {final_certificate} :\n"
        f"    tableInRoots {index} = {table_tail_normal(index, 0)} := by\n"
        f"  change SparsePolynomial.substitute (dummitTable {index}) "
        "elementaryPolynomials = _\n"
        f"  rw [{row_certificate}, {table_tail_certificate(index, 0)}]",
    ])
    return module


def theta_suffix_expression(start: int) -> str:
    entries = ", ".join(f"thetaPolynomial {index}"
                        for index in range(start, 6))
    return f"[{entries}]"


def root_state_normal(start: int, degree: int) -> str:
    return f"rootState{start}Degree{degree}Normal"


def root_state_product(start: int, degree: int) -> str:
    return f"rootState{start}Degree{degree}ProductNormal"


def root_state_certificate_module(start: int, degree: int) -> str:
    return f"{PREFIX}RootState{start}Degree{degree}Certificate"


def root_state_certificate(start: int, degree: int) -> str:
    return f"root_state{start}_degree{degree}_certificate"


def write_root_data() -> tuple[str, str]:
    theta_data = f"{PREFIX}RootThetaData"
    theta_certificate = f"{PREFIX}RootThetaCertificate"
    theta_declarations = [
        lean_polynomial(f"theta{index}Normal", THETAS[index])
        for index in range(6)
    ]
    write_module(theta_data, ["ComputableDummitCoefficientsCore"],
                 theta_declarations)
    write_module(theta_certificate, [theta_data], [
        decide_theorem(
            f"thetaPolynomial_{index}_certificate",
            f"thetaPolynomial {index} = theta{index}Normal",
            depth=100000)
        for index in range(6)
    ])

    state_data = f"{PREFIX}RootStateData"
    cache: dict[tuple[int, int], Polynomial] = {}
    declarations: list[str] = []
    for start in reversed(range(7)):
        for degree in range(7):
            declarations.append(lean_polynomial(
                root_state_normal(start, degree),
                esymm_state(start, degree, cache)))
            if start < 6 and degree > 0:
                declarations.append(lean_polynomial(
                    root_state_product(start, degree),
                    mul(THETAS[start],
                        esymm_state(start + 1, degree - 1, cache))))
    write_module(state_data, [theta_certificate], declarations)
    return theta_certificate, state_data


def write_root_state_certificates(theta_certificate: str,
                                  state_data: str) -> None:
    for start in reversed(range(7)):
        for degree in range(7):
            # The four large public coefficient certificates begin at
            # (start, degree) = (0, 3), ..., (0, 6).  Each recurrence step
            # either preserves or lowers the degree by one, so these are the
            # only unreachable low-degree states in the dependency closure.
            if degree < max(0, 3 - start):
                continue
            module = root_state_certificate_module(start, degree)
            normal = root_state_normal(start, degree)
            statement = (
                f"SparsePolynomial.esymm {theta_suffix_expression(start)} "
                f"{degree} = {normal}")
            if start == 6 or degree == 0:
                write_module(module, [state_data], [
                    decide_theorem(root_state_certificate(start, degree),
                                   statement, depth=100000),
                ])
                continue
            high_module = root_state_certificate_module(start + 1, degree)
            low_module = root_state_certificate_module(start + 1, degree - 1)
            product = root_state_product(start, degree)
            product_certificate = (
                f"root_state{start}_degree{degree}_product_certificate")
            merge_certificate = (
                f"root_state{start}_degree{degree}_merge_certificate")
            declarations = [
                decide_theorem(
                    product_certificate,
                    f"SparsePolynomial.mul theta{start}Normal "
                    f"{root_state_normal(start + 1, degree - 1)} = {product}"),
                decide_theorem(
                    merge_certificate,
                    f"SparsePolynomial.add {root_state_normal(start + 1, degree)} "
                    f"{product} = {normal}"),
                f"theorem {root_state_certificate(start, degree)} :\n"
                f"    {statement} := by\n"
                "  change SparsePolynomial.add\n"
                f"    (SparsePolynomial.esymm {theta_suffix_expression(start + 1)} "
                f"{degree})\n"
                f"    (SparsePolynomial.mul (thetaPolynomial {start})\n"
                f"      (SparsePolynomial.esymm {theta_suffix_expression(start + 1)} "
                f"{degree - 1})) = {normal}\n"
                f"  rw [thetaPolynomial_{start}_certificate,\n"
                f"    {root_state_certificate(start + 1, degree)},\n"
                f"    {root_state_certificate(start + 1, degree - 1)},\n"
                f"    {product_certificate}, {merge_certificate}]",
            ]
            write_module(module,
                         [state_data, theta_certificate, high_module, low_module],
                         declarations)


def write_root_final(index: int, table_final: str) -> str:
    degree = 6 - index
    sign = -1 if degree % 2 else 1
    word = table_word(index)
    module = f"{PREFIX}Root{index}Final"
    candidate = f"rootCoefficient{index}Candidate"
    final_certificate = f"root_coefficient_{word}_final_certificate"
    source_certificate = f"sparseRootCoefficient_{word}_certificate"
    common = table_tail_normal(index, 0)
    write_module(module,
        [table_final, root_state_certificate_module(0, degree)], [
        f"def {candidate} : SparsePolynomial :=\n"
        f"  SparsePolynomial.mul (SparsePolynomial.const {sign}) "
        f"{root_state_normal(0, degree)}",
        decide_theorem(final_certificate, f"{candidate} = {common}"),
        f"theorem {source_certificate} :\n"
        f"    sparseRootCoefficient {index} = {common} := by\n"
        f"  change SparsePolynomial.mul (SparsePolynomial.const {sign})\n"
        f"    (SparsePolynomial.esymm thetaPolynomials {degree}) = {common}\n"
        f"  rw [show thetaPolynomials = {theta_suffix_expression(0)} by rfl,\n"
        f"    {root_state_certificate(0, degree)}]\n"
        f"  change {candidate} = {common}\n"
        f"  exact {final_certificate}",
    ])
    return module


def write_all_certificates() -> None:
    rows = parse_table()
    table_finals: list[str] = []
    for index in range(4):
        row = rows[index]
        write_table_term_certificates(index, row)
        row_data, group_count = write_table_row_data(index, row)
        write_table_tail_certificates(index, row, row_data, group_count)
        table_finals.append(write_table_final(index, row, row_data))
    theta_certificate, state_data = write_root_data()
    write_root_state_certificates(theta_certificate, state_data)
    root_finals = [write_root_final(index, table_finals[index])
                   for index in range(4)]
    write_module(f"{PREFIX}s", root_finals, [])


def write_probe() -> None:
    # Largest raw accumulator multiplication among table rows zero through
    # three after `SparseTerm.substitute` was changed to `mulPowAccum`.
    term: Term = (1, (2, 4, 3, 0, 1))
    normal = substitute_term(term)
    contents = "\n\n".join([
        "import PolynomialFormulas.ComputableDummitCoefficientsCore",
        f"namespace {NAMESPACE}",
        "open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients",
        "set_option maxRecDepth 1000000",
        lean_polynomial("worstTableTermNormal", normal),
        """set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem worst_table_term_certificate :
    SparseTerm.substitute ⟨1, ⟨2, 4, 3, 0, 1⟩⟩
        elementaryPolynomials = worstTableTermNormal := by
  decide""",
        f"end {NAMESPACE}",
    ]) + "\n"
    (LEAN_DIR / f"{PREFIX}Probe.lean").write_text(contents)


def stats() -> None:
    rows = parse_table()
    for index in range(4):
        table = table_coefficient(rows[index])
        root = root_coefficient(index)
        accumulator_equal = all(
            substitute_term_accum(term) == substitute_term(term)
            for term in rows[index])
        print(index, "table terms", len(rows[index]),
              "normal terms", len(table), "root terms", len(root),
              "equal", table == root,
              "accumulator equal", accumulator_equal)
        sizes = [len(substitute_term(term)) for term in rows[index]]
        costs = [lean_substitute_cost(term) for term in rows[index]]
        print("  table expansion max", max(sizes), "sum", sum(sizes),
              "largest", sorted(sizes, reverse=True)[:8])
        print("  Lean raw-product max", max(cost[0] for cost in costs),
              "largest", sorted((cost[0] for cost in costs), reverse=True)[:8])
        worst = max(range(len(costs)), key=lambda position: costs[position][0])
        print("  worst table position", worst, "term", rows[index][worst],
              "cost", costs[worst])
    cache: dict[tuple[int, int], Polynomial] = {}
    root_products = []
    for start in range(6):
        for degree in range(1, 7):
            child = esymm_state(start + 1, degree - 1, cache)
            root_products.append((len(THETAS[start]) * len(child), start,
                                  degree, len(child)))
    print("root esymm largest raw products", sorted(root_products, reverse=True)[:10])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stats", action="store_true")
    parser.add_argument("--write-probe", action="store_true")
    parser.add_argument("--write-all", action="store_true")
    parser.add_argument(
        "--write-term-shards", nargs=2, type=int,
        metavar=("TABLE_INDEX", "TERM_POSITION"),
        help="regenerate one table-term certificate using accumulator shards")
    args = parser.parse_args()
    if args.stats:
        stats()
        return
    if args.write_probe:
        write_probe()
        return
    if args.write_term_shards:
        index, position = args.write_term_shards
        rows = parse_table()
        if not 0 <= index < 4:
            parser.error("TABLE_INDEX must be between 0 and 3")
        if not 0 <= position < len(rows[index]):
            parser.error(
                f"TERM_POSITION must be between 0 and {len(rows[index]) - 1} "
                f"for table {index}")
        WRITTEN_MODULES.clear()
        write_table_term_certificate_files(
            index, position, rows[index][position], force_sharded=True)
        write_target_manifest_and_check(index, position)
        return
    if args.write_all:
        write_all_certificates()
        return
    parser.error("generation modes will be added after validating source data")


if __name__ == "__main__":
    main()
