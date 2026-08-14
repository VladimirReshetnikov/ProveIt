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
import hashlib
import re
from collections import defaultdict
from collections.abc import Callable
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from pathlib import Path


Exponent = tuple[int, int, int, int, int]
Polynomial = dict[Exponent, int]
Term = tuple[int, Exponent]
TermList = list[Term]
ModuleEmitter = Callable[[str, list[str], list[str]], None]

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
FORCE_SHARDED_TABLE_TERMS = {(0, 51), (0, 120), (0, 125)}

# Tail merge sharding is an explicitly targeted recovery mode.  It is not
# selected by --write-all: direct tail output remains the default and stays
# byte-for-byte stable.  Each authorized target has four terms, hence three
# materialized intermediate sums and one final sum into the public normal.
AUTHORIZED_SHARDED_TABLE_TAILS = frozenset({
    (0, 0), (0, 4), (0, 11), (0, 15),
})
TAIL_MERGE_RAW_LIMIT = 16000
TAIL_MERGE_LITERAL_LIMIT = 9000
TAIL_SHARD_MODULE_COUNT = 9

# Root elementary-symmetric products have the opposite shape from table-term
# products: the left theta polynomial has only ten terms while the right child
# can have thousands.  Split the right operand, and only at the three exact
# product frontiers that cross the same 10,000-row normalization threshold.
ROOT_PRODUCT_NORMALIZE_SHARD_THRESHOLD = 10000
ROOT_RAW_RIGHT_CHUNK_SIZE = 1000
EXPECTED_SHARDED_ROOT_PRODUCTS = ((1, 5), (0, 5), (0, 6))
EXPECTED_ROOT_PRODUCT_MODULE_COUNTS = {
    (1, 5): 139,
    (0, 5): 160,
    (0, 6): 212,
}
EXPECTED_ROOT_PRODUCT_SHAPES = {
    # child terms, raw terms, right chunks, buckets per radix coordinate
    (1, 5): (1583, 15830, 2, (11, 11, 11, 11, 11)),
    (0, 5): (2135, 21350, 3, (11, 11, 11, 11, 11)),
    (0, 6): (4011, 40110, 5, (13, 13, 13, 13, 13)),
}
EXPECTED_ROOT_MODULE_COUNT = 563


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
ASCII_DIGITS = "0123456789"


def write_module(name: str, imports: list[str], declarations: list[str]) -> None:
    (LEAN_DIR / f"{name}.lean").write_text(module_text(imports, declarations))
    WRITTEN_MODULES.add(name)


def owns_table_term_target(name: str, index: int, position: int) -> bool:
    """Whether a module or filename belongs to one exact table term."""
    target_prefix = f"{PREFIX}Table{index}Term{position}"
    if not name.startswith(target_prefix):
        return False
    suffix = name[len(target_prefix):]
    return not suffix or suffix[0] not in ASCII_DIGITS


def write_target_manifest_and_check(index: int, position: int) -> None:
    """Record and reject stale generated shards for one exact table term.

    This is deliberately non-destructive: the target-scoped manifest makes
    every generated source explicit, and an obsolete shard causes generation
    to fail with its exact filename instead of deleting through a broad glob.
    """
    target_prefix = f"{PREFIX}Table{index}Term{position}"
    expected = sorted(
        f"{module}.lean" for module in WRITTEN_MODULES
        if owns_table_term_target(module, index, position)
    )
    manifest = LEAN_DIR / f"{target_prefix}GeneratedFiles.txt"
    manifest.write_text("\n".join(expected) + "\n")
    existing = {
        path.name for path in LEAN_DIR.glob(f"{target_prefix}*.lean")
        if owns_table_term_target(path.name, index, position)
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


def table_tail_merge_step_data_module(
        index: int, group: int, step: int) -> str:
    return f"{PREFIX}Table{index}Tail{group}MergeStep{step}Data"


def table_tail_merge_step_certificate_module(
        index: int, group: int, step: int) -> str:
    return f"{PREFIX}Table{index}Tail{group}MergeStep{step}Certificate"


def table_tail_merge_step_normal(
        index: int, group: int, step: int) -> str:
    return f"table{index}Tail{group}MergeStep{step}Normal"


def table_tail_merge_step_certificate(
        index: int, group: int, step: int) -> str:
    return f"table{index}_tail{group}_merge_step{step}_certificate"


def table_tail_target_prefix(index: int, group: int) -> str:
    return f"{PREFIX}Table{index}Tail{group}"


def owns_table_tail_target(name: str, index: int, group: int) -> bool:
    """Whether a module or filename belongs to one exact table tail."""
    target_prefix = table_tail_target_prefix(index, group)
    if not name.startswith(target_prefix):
        return False
    suffix = name[len(target_prefix):]
    return not suffix or suffix[0] not in ASCII_DIGITS


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


@lru_cache(maxsize=None)
def tail_direct_term_polynomial(term: Term) -> Polynomial:
    """Cached direct expansion used only by targeted tail rendering."""
    return substitute_term(term)


@lru_cache(maxsize=None)
def tail_accum_term_polynomial(term: Term) -> Polynomial:
    """Independent factor-at-a-time expansion for tail validation."""
    return substitute_term_accum(term)


def independent_polynomial_add(
        left: Polynomial, right: Polynomial) -> Polynomial:
    """Add two sparse maps without calling the generator's variadic add."""
    result = dict(right)
    for exponent, coefficient in left.items():
        combined = result.get(exponent, 0) + coefficient
        if combined:
            result[exponent] = combined
        else:
            result.pop(exponent, None)
    return result


@dataclass(frozen=True)
class TailMergeShardPlan:
    index: int
    group: int
    positions: tuple[int, int, int, int]
    terms: tuple[Term, Term, Term, Term]
    term_normals: tuple[Polynomial, Polynomial, Polynomial, Polynomial]
    next_normal: Polynomial
    stage_normals: tuple[Polynomial, Polynomial, Polynomial, Polynomial]
    raw_sizes: tuple[int, int, int, int]


def require_authorized_tail_shard_target(index: int, group: int) -> None:
    if (index, group) not in AUTHORIZED_SHARDED_TABLE_TAILS:
        allowed = ", ".join(
            f"({table}, {tail})"
            for table, tail in sorted(AUTHORIZED_SHARDED_TABLE_TAILS))
        raise RuntimeError(
            f"unauthorized sharded table tail ({index}, {group}); "
            f"allowed targets: {allowed}")


def tail_merge_shard_plan(
        index: int, group: int, row: list[Term]) -> TailMergeShardPlan:
    """Plan one authorized four-add tail merge entirely in memory."""
    require_authorized_tail_shard_target(index, group)
    start = group * TABLE_BLOCK_SIZE
    stop = start + TABLE_BLOCK_SIZE
    if stop > len(row):
        raise RuntimeError(
            f"table {index} tail {group} must contain exactly "
            f"{TABLE_BLOCK_SIZE} terms")
    positions = tuple(range(start, stop))
    if len(positions) != TABLE_BLOCK_SIZE:
        raise RuntimeError("tail shard position count changed")
    terms = tuple(row[position] for position in positions)
    term_normals = tuple(
        tail_direct_term_polynomial(term) for term in terms)
    next_normal: Polynomial = {}
    for term in row[stop:]:
        next_normal = add(next_normal, tail_direct_term_polynomial(term))

    stages: list[Polynomial | None] = [None] * TABLE_BLOCK_SIZE
    raw_sizes: list[int] = [0] * TABLE_BLOCK_SIZE
    accumulator = next_normal
    for step in reversed(range(TABLE_BLOCK_SIZE)):
        raw_sizes[step] = len(term_normals[step]) + len(accumulator)
        accumulator = add(term_normals[step], accumulator)
        stages[step] = accumulator
    if any(stage is None for stage in stages):
        raise RuntimeError("incomplete tail merge shard stages")
    stage_normals = tuple(stage for stage in stages if stage is not None)
    if len(stage_normals) != TABLE_BLOCK_SIZE:
        raise RuntimeError("tail merge shard stage count changed")
    plan = TailMergeShardPlan(
        index=index,
        group=group,
        positions=positions,
        terms=terms,
        term_normals=term_normals,
        next_normal=next_normal,
        stage_normals=stage_normals,
        raw_sizes=tuple(raw_sizes),
    )
    validate_tail_merge_shard_plan(plan, row)
    return plan


def validate_tail_merge_shard_plan(
        plan: TailMergeShardPlan, row: list[Term]) -> None:
    """Independently recheck every finite addition and resource bound."""
    require_authorized_tail_shard_target(plan.index, plan.group)
    start = plan.group * TABLE_BLOCK_SIZE
    expected_positions = tuple(range(start, start + TABLE_BLOCK_SIZE))
    if plan.positions != expected_positions:
        raise RuntimeError("tail merge shard positions changed")
    if start + TABLE_BLOCK_SIZE > len(row):
        raise RuntimeError("tail merge shard target is not a full block")
    expected_terms = tuple(row[position] for position in expected_positions)
    if plan.terms != expected_terms:
        raise RuntimeError("tail merge shard terms changed")
    if (len(plan.term_normals) != TABLE_BLOCK_SIZE or
            len(plan.stage_normals) != TABLE_BLOCK_SIZE or
            len(plan.raw_sizes) != TABLE_BLOCK_SIZE):
        raise RuntimeError("tail merge shard trace must have four stages")

    expected_term_normals = tuple(
        tail_accum_term_polynomial(term) for term in expected_terms)
    if plan.term_normals != expected_term_normals:
        raise RuntimeError("tail merge direct and accumulator expansions differ")

    expected_next: Polynomial = {}
    for term in row[start + TABLE_BLOCK_SIZE:]:
        expected_next = independent_polynomial_add(
            expected_next, tail_accum_term_polynomial(term))
    if plan.next_normal != expected_next:
        raise RuntimeError("tail merge next-tail normal changed")

    accumulator = expected_next
    for step in reversed(range(TABLE_BLOCK_SIZE)):
        raw_size = len(expected_term_normals[step]) + len(accumulator)
        if plan.raw_sizes[step] != raw_size:
            raise RuntimeError(
                f"tail merge step {step} raw size changed")
        if raw_size > TAIL_MERGE_RAW_LIMIT:
            raise RuntimeError(
                f"tail merge step {step} raw size {raw_size} exceeds "
                f"limit {TAIL_MERGE_RAW_LIMIT}")
        accumulator = independent_polynomial_add(
            expected_term_normals[step], accumulator)
        if plan.stage_normals[step] != accumulator:
            raise RuntimeError(
                f"tail merge step {step} arithmetic changed")
        if len(accumulator) > TAIL_MERGE_LITERAL_LIMIT:
            raise RuntimeError(
                f"tail merge step {step} literal size {len(accumulator)} "
                f"exceeds limit {TAIL_MERGE_LITERAL_LIMIT}")
        if any(coefficient == 0 for coefficient in accumulator.values()):
            raise RuntimeError(
                f"tail merge step {step} contains a zero coefficient")


def expected_tail_shard_modules(index: int, group: int) -> tuple[str, ...]:
    require_authorized_tail_shard_target(index, group)
    modules = (
        table_tail_data_module(index, group),
        *(table_tail_merge_step_data_module(index, group, step)
          for step in (3, 2, 1)),
        *(table_tail_merge_step_certificate_module(index, group, step)
          for step in (3, 2, 1, 0)),
        table_tail_certificate_module(index, group),
    )
    if (len(modules) != TAIL_SHARD_MODULE_COUNT or
            len(set(modules)) != len(modules)):
        raise RuntimeError(
            f"tail shard target must own exactly {TAIL_SHARD_MODULE_COUNT} "
            f"distinct modules")
    return modules


def tail_public_certificate_declaration(
        index: int, group: int, row: list[Term],
        positions: tuple[int, int, int, int]) -> str:
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
    return (
        f"theorem {table_tail_certificate(index, group)} :\n"
        f"    SparsePolynomial.substitute table{index}Tail{group} "
        f"elementaryPolynomials = {table_tail_normal(index, group)} := by\n"
        f"  change {changed} = {table_tail_normal(index, group)}\n"
        f"  rw [{', '.join(rewrites)}]\n"
        f"  exact table{index}_tail{group}_merge_certificate")


def render_tail_shard_target(
        index: int, group: int, row: list[Term]
        ) -> tuple[dict[str, str], dict[str, tuple[str, ...]]]:
    """Render and validate one nine-module tail shard graph in memory."""
    plan = tail_merge_shard_plan(index, group, row)
    rendered: dict[str, str] = {}
    imports_by_module: dict[str, tuple[str, ...]] = {}

    def collect(name: str, imports: list[str], declarations: list[str]) -> None:
        if name in rendered:
            raise RuntimeError(f"duplicate generated tail module: {name}")
        rendered[name] = module_text(imports, declarations)
        imports_by_module[name] = tuple(imports)

    positions = plan.positions
    tail_data = table_tail_data_module(index, group)
    tail_normal = table_tail_normal(index, group)
    next_normal = table_tail_normal(index, group + 1)
    normal_terms = [table_term_normal(index, position)
                    for position in positions]
    candidate = nested_add(normal_terms, next_normal)
    data_imports = [
        f"{PREFIX}Table{index}RowData",
        table_tail_certificate_module(index, group + 1),
        *(table_term_certificate_module(index, position)
          for position in positions),
    ]
    collect(tail_data, data_imports, [
        lean_polynomial(tail_normal, plan.stage_normals[0]),
        f"def table{index}Tail{group}Candidate : SparsePolynomial :=\n"
        f"  {candidate}",
    ])

    for step in (3, 2, 1):
        collect(
            table_tail_merge_step_data_module(index, group, step),
            [tail_data],
            [lean_polynomial(
                table_tail_merge_step_normal(index, group, step),
                plan.stage_normals[step])])

    for step in (3, 2, 1, 0):
        left = table_term_normal(index, positions[step])
        right = (next_normal if step == 3 else
                 table_tail_merge_step_normal(index, group, step + 1))
        result = (tail_normal if step == 0 else
                  table_tail_merge_step_normal(index, group, step))
        if step == 3:
            imports = [
                table_tail_merge_step_data_module(index, group, 3)]
        elif step == 0:
            imports = [
                tail_data,
                table_tail_merge_step_data_module(index, group, 1),
            ]
        else:
            imports = [
                table_tail_merge_step_data_module(index, group, step),
                table_tail_merge_step_data_module(index, group, step + 1),
            ]
        collect(
            table_tail_merge_step_certificate_module(index, group, step),
            imports,
            [decide_theorem(
                table_tail_merge_step_certificate(index, group, step),
                f"SparsePolynomial.add {left} {right} = {result}")])

    merge_name = f"table{index}_tail{group}_merge_certificate"
    merge_certificates = [
        table_tail_merge_step_certificate(index, group, step)
        for step in (3, 2, 1, 0)
    ]
    merge_declaration = (
        f"theorem {merge_name} :\n"
        f"    table{index}Tail{group}Candidate = {tail_normal} := by\n"
        f"  change {candidate} = {tail_normal}\n"
        f"  rw [{', '.join(merge_certificates)}]")
    tail_certificate = table_tail_certificate_module(index, group)
    collect(
        tail_certificate,
        [tail_data,
         *(table_tail_merge_step_certificate_module(index, group, step)
           for step in (3, 2, 1, 0))],
        [merge_declaration,
         tail_public_certificate_declaration(
             index, group, row, positions)])

    validate_tail_shard_graph(plan, row, rendered, imports_by_module)
    return rendered, imports_by_module


def expected_tail_shard_imports(
        index: int, group: int,
        positions: tuple[int, int, int, int]
        ) -> dict[str, tuple[str, ...]]:
    tail_data = table_tail_data_module(index, group)
    result: dict[str, tuple[str, ...]] = {
        tail_data: (
            f"{PREFIX}Table{index}RowData",
            table_tail_certificate_module(index, group + 1),
            *(table_term_certificate_module(index, position)
              for position in positions),
        ),
    }
    for step in (3, 2, 1):
        result[table_tail_merge_step_data_module(index, group, step)] = (
            tail_data,)
    result[table_tail_merge_step_certificate_module(index, group, 3)] = (
        table_tail_merge_step_data_module(index, group, 3),)
    for step in (2, 1):
        result[table_tail_merge_step_certificate_module(
            index, group, step)] = (
                table_tail_merge_step_data_module(index, group, step),
                table_tail_merge_step_data_module(index, group, step + 1),
            )
    result[table_tail_merge_step_certificate_module(index, group, 0)] = (
        tail_data,
        table_tail_merge_step_data_module(index, group, 1),
    )
    result[table_tail_certificate_module(index, group)] = (
        tail_data,
        *(table_tail_merge_step_certificate_module(index, group, step)
          for step in (3, 2, 1, 0)),
    )
    return result


def validate_tail_shard_graph(
        plan: TailMergeShardPlan, row: list[Term],
        rendered: dict[str, str],
        imports_by_module: dict[str, tuple[str, ...]]) -> None:
    """Fail closed on names, bytes, imports, DAG, trust, and public API."""
    validate_tail_merge_shard_plan(plan, row)
    expected = set(expected_tail_shard_modules(plan.index, plan.group))
    if (set(rendered) != expected or
            set(imports_by_module) != expected):
        raise RuntimeError(
            "rendered tail module set does not match its owner set")
    expected_imports = expected_tail_shard_imports(
        plan.index, plan.group, plan.positions)
    if imports_by_module != expected_imports:
        raise RuntimeError("rendered tail import graph changed")
    duplicate_imports = sorted(
        module for module, imports in imports_by_module.items()
        if len(imports) != len(set(imports)))
    if duplicate_imports:
        raise RuntimeError(
            "duplicate generated tail imports: "
            + ", ".join(duplicate_imports))

    allowed_external = set(expected_imports[
        table_tail_data_module(plan.index, plan.group)])
    external = {
        dependency
        for imports in imports_by_module.values()
        for dependency in imports
        if dependency not in expected
    }
    if external != allowed_external:
        raise RuntimeError(
            "unexpected tail external imports: "
            + ", ".join(sorted(external ^ allowed_external)))

    visited: set[str] = set()
    active: set[str] = set()

    def visit(module: str) -> None:
        if module in active:
            raise RuntimeError(f"cycle in generated tail imports at {module}")
        if module in visited:
            return
        active.add(module)
        for dependency in imports_by_module[module]:
            if dependency in expected:
                visit(dependency)
        active.remove(module)
        visited.add(module)

    aggregate = table_tail_certificate_module(plan.index, plan.group)
    visit(aggregate)
    if visited != expected:
        unreachable = ", ".join(sorted(expected - visited))
        raise RuntimeError(
            f"generated tail modules unreachable from aggregate: "
            f"{unreachable}")

    forbidden = re.compile(
        r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b|"
        r"implemented_by|Lean\.ofReduceBool")
    declared_by_module: dict[str, tuple[str, ...]] = {}
    for module, payload in rendered.items():
        heartbeats = [int(value) for value in re.findall(
            r"set_option maxHeartbeats (\d+)", payload)]
        if (not heartbeats or
                any(value <= 0 or value > 20000000
                    for value in heartbeats)):
            raise RuntimeError(
                f"tail module {module} lacks a finite heartbeat bound")
        if forbidden.search(payload):
            raise RuntimeError(f"untrusted tail proof text in {module}")
        declarations = tuple(re.findall(
            r"(?m)^(?:def|theorem)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
            payload))
        if len(declarations) != len(set(declarations)):
            raise RuntimeError(
                f"duplicate declarations in generated tail module {module}")
        declared_by_module[module] = declarations

    index, group = plan.index, plan.group
    tail_data = table_tail_data_module(index, group)
    expected_declarations: dict[str, tuple[str, ...]] = {
        tail_data: (
            table_tail_normal(index, group),
            f"table{index}Tail{group}Candidate",
        ),
        **{
            table_tail_merge_step_data_module(index, group, step): (
                table_tail_merge_step_normal(index, group, step),)
            for step in (3, 2, 1)
        },
        **{
            table_tail_merge_step_certificate_module(index, group, step): (
                table_tail_merge_step_certificate(index, group, step),)
            for step in (3, 2, 1, 0)
        },
        table_tail_certificate_module(index, group): (
            f"table{index}_tail{group}_merge_certificate",
            table_tail_certificate(index, group),
        ),
    }
    if declared_by_module != expected_declarations:
        raise RuntimeError("generated tail declaration names changed")
    all_declarations = [
        declaration
        for declarations in declared_by_module.values()
        for declaration in declarations
    ]
    if len(all_declarations) != len(set(all_declarations)):
        raise RuntimeError("generated tail declarations are not unique")

    if lean_polynomial(
            table_tail_normal(index, group),
            plan.stage_normals[0]) not in rendered[tail_data]:
        raise RuntimeError("public tail result literal changed")
    for step in (3, 2, 1):
        module = table_tail_merge_step_data_module(index, group, step)
        literal = lean_polynomial(
            table_tail_merge_step_normal(index, group, step),
            plan.stage_normals[step])
        if literal not in rendered[module]:
            raise RuntimeError(
                f"tail merge step {step} result literal changed")

    certificate_module = table_tail_certificate_module(index, group)
    public_payload = rendered[certificate_module]
    merge_statement = (
        f"theorem table{index}_tail{group}_merge_certificate :\n"
        f"    table{index}Tail{group}Candidate = "
        f"{table_tail_normal(index, group)} := by")
    final_declaration = tail_public_certificate_declaration(
        index, group, row, plan.positions)
    if merge_statement not in public_payload:
        raise RuntimeError("public tail merge endpoint changed")
    if final_declaration not in public_payload:
        raise RuntimeError("public tail certificate endpoint changed")
    if "  decide" in public_payload:
        raise RuntimeError("public tail merge must compose isolated proofs")
    ordered_rw = ", ".join(
        table_tail_merge_step_certificate(index, group, step)
        for step in (3, 2, 1, 0))
    if f"  rw [{ordered_rw}]" not in public_payload:
        raise RuntimeError("public tail merge rewrite chain changed")


def tail_shard_manifest_name(index: int, group: int) -> str:
    return f"{table_tail_target_prefix(index, group)}GeneratedFiles.txt"


def tail_shard_manifest_bytes(rendered: dict[str, str]) -> bytes:
    return ("".join(f"{module}.lean\n" for module in sorted(rendered))
            .encode("utf-8"))


def existing_owned_tail_paths(
        index: int, group: int, lean_dir: Path = LEAN_DIR) -> set[Path]:
    """Existing source paths owned by one exact decimal-bounded tail."""
    prefix = table_tail_target_prefix(index, group)
    paths = {
        path for path in lean_dir.glob(f"{prefix}*.lean")
        if owns_table_tail_target(path.name, index, group)
    }
    manifest = lean_dir / tail_shard_manifest_name(index, group)
    if manifest.exists() or manifest.is_symlink():
        paths.add(manifest)
    return paths


def validate_existing_tail_paths(
        index: int, group: int, expected: set[str],
        lean_dir: Path = LEAN_DIR) -> set[Path]:
    paths = existing_owned_tail_paths(index, group, lean_dir)
    for filename in expected:
        path = lean_dir / filename
        if path.is_symlink():
            paths.add(path)
    invalid = sorted(
        str(path) for path in paths
        if path.is_symlink() or not path.is_file())
    if invalid:
        raise RuntimeError(
            "refusing non-regular generated tail paths:\n  "
            + "\n  ".join(invalid))
    return paths


def tail_shard_file_payloads(rendered: dict[str, str],
                             index: int, group: int) -> dict[str, bytes]:
    expected_modules = set(expected_tail_shard_modules(index, group))
    if set(rendered) != expected_modules:
        raise RuntimeError("tail shard payload module set changed")
    payloads = {
        f"{module}.lean": rendered[module].encode("utf-8")
        for module in rendered
    }
    payloads[tail_shard_manifest_name(index, group)] = \
        tail_shard_manifest_bytes(rendered)
    return payloads


def tail_shard_differences(
        rendered: dict[str, str], index: int, group: int,
        lean_dir: Path = LEAN_DIR
        ) -> tuple[list[str], list[str], list[str]]:
    """Return missing, unexpected, and byte-stale target filenames."""
    payloads = tail_shard_file_payloads(rendered, index, group)
    expected = set(payloads)
    paths = validate_existing_tail_paths(index, group, expected, lean_dir)
    existing = {path.name for path in paths}
    missing = sorted(expected - existing)
    unexpected = sorted(existing - expected)
    stale = sorted(
        filename for filename in expected & existing
        if (lean_dir / filename).read_bytes() != payloads[filename])
    return missing, unexpected, stale


def format_tail_shard_differences(
        index: int, group: int, missing: list[str],
        unexpected: list[str], stale: list[str]) -> str:
    lines = [f"table {index} tail {group} shard check failed"]
    for label, filenames in (
            ("missing", missing),
            ("unexpected", unexpected),
            ("stale-content", stale)):
        if filenames:
            lines.append(f"  {label} ({len(filenames)}):")
            lines.extend(f"    {filename}" for filename in filenames)
    return "\n".join(lines)


def tail_shard_digest(rendered: dict[str, str]) -> str:
    digest = hashlib.sha256()
    for module in sorted(rendered):
        digest.update(module.encode("utf-8"))
        digest.update(b"\0")
        digest.update(rendered[module].encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest()


def check_tail_shard_target(
        index: int, group: int, row: list[Term],
        lean_dir: Path = LEAN_DIR) -> str:
    rendered, _ = render_tail_shard_target(index, group, row)
    missing, unexpected, stale = tail_shard_differences(
        rendered, index, group, lean_dir)
    if missing or unexpected or stale:
        raise RuntimeError(format_tail_shard_differences(
            index, group, missing, unexpected, stale))
    return tail_shard_digest(rendered)


def write_tail_shard_target(
        index: int, group: int, row: list[Term],
        lean_dir: Path = LEAN_DIR) -> str:
    """Reconcile one target after full in-memory render and preflight."""
    rendered, _ = render_tail_shard_target(index, group, row)
    payloads = tail_shard_file_payloads(rendered, index, group)
    _, unexpected, _ = tail_shard_differences(
        rendered, index, group, lean_dir)
    if unexpected:
        raise RuntimeError(format_tail_shard_differences(
            index, group, [], unexpected, []))
    for filename in sorted(payloads):
        path = lean_dir / filename
        payload = payloads[filename]
        if not path.exists() or path.read_bytes() != payload:
            path.write_bytes(payload)
    return check_tail_shard_target(index, group, row, lean_dir)


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


def root_state_keys() -> tuple[tuple[int, int], ...]:
    """The exact dependency closure of the four public root coefficients."""
    return tuple(
        (start, degree)
        for start in reversed(range(7))
        for degree in range(7)
        if degree >= max(0, 3 - start)
    )


def root_table_final_module(index: int) -> str:
    return f"{PREFIX}Table{index}Final"


ROOT_NORMALIZE_SUPPORT_MODULE = f"{PREFIX}RootNormalizeSupport"
ROOT_RAW_MUL_APPEND_LEFT_CERTIFICATE = "root_rawMul_append_left"
ROOT_RAW_MUL_SINGLETON_APPEND_RIGHT_CERTIFICATE = \
    "root_rawMul_singleton_append_right"
ROOT_FLATTEN_BUCKETS_APPEND_CERTIFICATE = "root_flattenBuckets_append"
ROOT_FLATTEN_BUCKETS_SINGLETON_CERTIFICATE = "root_flattenBuckets_singleton"


def root_product_module(start: int, degree: int, suffix: str) -> str:
    return f"{PREFIX}RootState{start}Degree{degree}Product{suffix}"


def root_product_normal(start: int, degree: int, suffix: str) -> str:
    return f"rootState{start}Degree{degree}Product{suffix}Normal"


def root_product_aux_certificate(
        start: int, degree: int, suffix: str) -> str:
    return (f"root_state{start}_degree{degree}_product_"
            f"{suffix}_certificate")


def root_state_product_certificate(start: int, degree: int) -> str:
    """The pre-existing theorem name consumed by root-state recurrence."""
    return f"root_state{start}_degree{degree}_product_certificate"


def root_product_left_normal(start: int, degree: int, left: int) -> str:
    return root_product_normal(start, degree, f"RawLeft{left}")


def root_product_right_module(
        start: int, degree: int, right: int) -> str:
    return root_product_module(start, degree, f"RawRightChunk{right}Data")


def root_product_right_normal(
        start: int, degree: int, right: int) -> str:
    return root_product_normal(start, degree, f"RawRightChunk{right}")


def root_product_pair_module(
        start: int, degree: int, left: int, right: int,
        suffix: str) -> str:
    return root_product_module(
        start, degree, f"RawChunkLeft{left}Right{right}{suffix}")


def root_product_pair_normal(
        start: int, degree: int, left: int, right: int) -> str:
    return root_product_normal(
        start, degree, f"RawChunkLeft{left}Right{right}")


def root_product_pair_certificate(
        start: int, degree: int, left: int, right: int) -> str:
    return root_product_aux_certificate(
        start, degree, f"raw_chunk_left{left}_right{right}")


def root_product_radix_bucket_module(
        start: int, degree: int, coordinate: int, bucket: int) -> str:
    return root_product_module(
        start, degree,
        f"NormalizeRadix{coordinate}Bucket{bucket}Data")


def root_product_radix_bucket_normal(
        start: int, degree: int, coordinate: int, bucket: int) -> str:
    return root_product_normal(
        start, degree, f"NormalizeRadix{coordinate}Bucket{bucket}")


def root_nested_append(expressions: list[str]) -> str:
    """Right-associated append used only by the fail-closed root emitter."""
    if not expressions:
        raise RuntimeError("cannot render an empty root append expression")
    result = expressions[-1]
    for expression in reversed(expressions[:-1]):
        result = f"({expression} ++ {result})"
    return result


@dataclass(frozen=True)
class RootProductShardPlan:
    start: int
    degree: int
    theta_terms: TermList
    child_terms: TermList
    right_chunks: list[TermList]
    pair_chunks: list[list[TermList]]
    raw_terms: TermList
    radix_stages: list[tuple[int, list[TermList], TermList]]
    product: Polynomial


def validate_root_product_shard_plan(plan: RootProductShardPlan) -> None:
    """Recheck a shard trace independently, including cached mutable data."""
    key = (plan.start, plan.degree)
    if key not in EXPECTED_SHARDED_ROOT_PRODUCTS:
        raise RuntimeError(f"unexpected sharded root product {key}")
    expected_child_terms, expected_raw_terms, expected_right_chunks, \
        expected_bucket_counts = EXPECTED_ROOT_PRODUCT_SHAPES[key]
    theta_terms = polynomial_terms(THETAS[plan.start])
    child = esymm_state(plan.start + 1, plan.degree - 1)
    child_terms = polynomial_terms(child)
    if plan.theta_terms != theta_terms or len(theta_terms) != 10:
        raise RuntimeError(f"root product {key} theta trace changed")
    if (plan.child_terms != child_terms or
            len(child_terms) != expected_child_terms):
        raise RuntimeError(f"root product {key} child trace changed")
    if (len(plan.right_chunks) != expected_right_chunks or
            any(not chunk or len(chunk) > ROOT_RAW_RIGHT_CHUNK_SIZE
                for chunk in plan.right_chunks) or
            [term for chunk in plan.right_chunks for term in chunk] !=
            child_terms):
        raise RuntimeError(f"root product {key} right-chunk trace changed")
    if len(plan.pair_chunks) != len(theta_terms):
        raise RuntimeError(f"root product {key} pair-row count changed")
    for left, (term, row) in enumerate(
            zip(theta_terms, plan.pair_chunks)):
        if len(row) != expected_right_chunks:
            raise RuntimeError(
                f"root product {key} pair-row {left} width changed")
        for right, (right_chunk, pair_chunk) in enumerate(
                zip(plan.right_chunks, row)):
            if (len(pair_chunk) > ROOT_RAW_RIGHT_CHUNK_SIZE or
                    pair_chunk != raw_mul_term_lists([term], right_chunk)):
                raise RuntimeError(
                    f"root product {key} raw pair ({left}, {right}) changed")
    expected_raw = raw_mul_term_lists(theta_terms, child_terms)
    reconstructed_raw = [
        term
        for row in plan.pair_chunks
        for pair_chunk in row
        for term in pair_chunk
    ]
    if (plan.raw_terms != reconstructed_raw or
            plan.raw_terms != expected_raw or
            len(plan.raw_terms) != expected_raw_terms or
            len(plan.raw_terms) < ROOT_PRODUCT_NORMALIZE_SHARD_THRESHOLD):
        raise RuntimeError(f"root product {key} raw trace changed")
    if len(plan.radix_stages) != 5:
        raise RuntimeError(f"root product {key} radix stage count changed")
    terms = plan.raw_terms
    for stage_index, (coordinate, buckets, flattened) in enumerate(
            plan.radix_stages):
        expected_coordinate = 4 - stage_index
        expected_buckets = bucketize_terms(terms, expected_coordinate)
        expected_flattened = radix_pass_terms(terms, expected_coordinate)
        if (coordinate != expected_coordinate or
                len(buckets) != expected_bucket_counts[stage_index] or
                buckets != expected_buckets or
                flattened != expected_flattened or
                flattened != [term for bucket in buckets for term in bucket]):
            raise RuntimeError(
                f"root product {key} radix-{expected_coordinate} trace changed")
        terms = flattened
    expected_product = mul(THETAS[plan.start], child)
    if (plan.product != expected_product or
            combine_terms(terms) != expected_product):
        raise RuntimeError(f"root product {key} combine trace changed")


@lru_cache(maxsize=1)
def sharded_root_product_keys() -> tuple[tuple[int, int], ...]:
    """Select and independently pin the expensive reachable root products."""
    cache: dict[tuple[int, int], Polynomial] = {}
    selected = tuple(
        (start, degree)
        for start, degree in root_state_keys()
        if start < 6 and degree > 0 and
        len(THETAS[start]) *
        len(esymm_state(start + 1, degree - 1, cache)) >=
        ROOT_PRODUCT_NORMALIZE_SHARD_THRESHOLD
    )
    if selected != EXPECTED_SHARDED_ROOT_PRODUCTS:
        raise RuntimeError(
            "root-product shard frontier changed: expected "
            f"{sorted(EXPECTED_SHARDED_ROOT_PRODUCTS)}, got "
            f"{sorted(selected)}")
    return selected


@lru_cache(maxsize=None)
def root_product_shard_plan(start: int, degree: int) -> RootProductShardPlan:
    """Compute and validate every finite stage of one root product shard."""
    if (start, degree) not in EXPECTED_SHARDED_ROOT_PRODUCTS:
        raise RuntimeError(
            f"unexpected sharded root product ({start}, {degree})")
    theta_terms = polynomial_terms(THETAS[start])
    child = esymm_state(start + 1, degree - 1)
    child_terms = polynomial_terms(child)
    expected_child_terms, expected_raw_terms, expected_right_chunks, \
        expected_bucket_counts = EXPECTED_ROOT_PRODUCT_SHAPES[(start, degree)]
    if len(theta_terms) != 10 or len(child_terms) != expected_child_terms:
        raise RuntimeError(
            f"root product ({start}, {degree}) source shape changed: "
            f"theta={len(theta_terms)}, child={len(child_terms)}")
    right_chunks = [
        child_terms[offset:offset + ROOT_RAW_RIGHT_CHUNK_SIZE]
        for offset in range(0, len(child_terms), ROOT_RAW_RIGHT_CHUNK_SIZE)
    ]
    if not right_chunks or any(
            not chunk or len(chunk) > ROOT_RAW_RIGHT_CHUNK_SIZE
            for chunk in right_chunks):
        raise RuntimeError(
            f"invalid right chunks for root product ({start}, {degree})")
    if [term for chunk in right_chunks for term in chunk] != child_terms:
        raise RuntimeError(
            f"right chunks do not reconstruct root product ({start}, {degree})")
    if len(right_chunks) != expected_right_chunks:
        raise RuntimeError(
            f"root product ({start}, {degree}) must have exactly "
            f"{expected_right_chunks} right chunks, got {len(right_chunks)}")

    pair_chunks = [
        [raw_mul_term_lists([term], right_chunk)
         for right_chunk in right_chunks]
        for term in theta_terms
    ]
    raw_terms = [
        term
        for left_row in pair_chunks
        for pair_chunk in left_row
        for term in pair_chunk
    ]
    expected_raw = raw_mul_term_lists(theta_terms, child_terms)
    if raw_terms != expected_raw:
        raise RuntimeError(
            f"raw chunks do not reconstruct root product ({start}, {degree})")
    if len(raw_terms) != expected_raw_terms:
        raise RuntimeError(
            f"root product ({start}, {degree}) raw size changed: expected "
            f"{expected_raw_terms}, got {len(raw_terms)}")
    if any(len(chunk) > ROOT_RAW_RIGHT_CHUNK_SIZE
           for row in pair_chunks for chunk in row):
        raise RuntimeError(
            f"raw chunk bound exceeded for root product ({start}, {degree})")

    radix_stages: list[tuple[int, list[TermList], TermList]] = []
    terms = raw_terms
    for coordinate in reversed(range(5)):
        buckets = bucketize_terms(terms, coordinate)
        flattened = [term for bucket in buckets for term in bucket]
        if flattened != radix_pass_terms(terms, coordinate):
            raise RuntimeError(
                "radix buckets do not reconstruct coordinate "
                f"{coordinate} for root product ({start}, {degree})")
        radix_stages.append((coordinate, buckets, flattened))
        terms = flattened
    coordinates = tuple(stage[0] for stage in radix_stages)
    bucket_counts = tuple(len(stage[1]) for stage in radix_stages)
    if coordinates != (4, 3, 2, 1, 0) or \
            bucket_counts != expected_bucket_counts:
        raise RuntimeError(
            f"root product ({start}, {degree}) radix shape changed: "
            f"coordinates={coordinates}, buckets={bucket_counts}")

    product = mul(THETAS[start], child)
    if combine_terms(terms) != product:
        raise RuntimeError(
            f"radix/combine trace failed for root product ({start}, {degree})")
    if len(raw_terms) < ROOT_PRODUCT_NORMALIZE_SHARD_THRESHOLD:
        raise RuntimeError(
            f"sharded root product below trigger ({start}, {degree})")
    plan = RootProductShardPlan(
        start, degree, theta_terms, child_terms, right_chunks,
        pair_chunks, raw_terms, radix_stages, product)
    validate_root_product_shard_plan(plan)
    return plan


def root_product_shard_modules(plan: RootProductShardPlan) -> tuple[str, ...]:
    """Enumerate one shard graph independently of the module emitter."""
    validate_root_product_shard_plan(plan)
    start, degree = plan.start, plan.degree
    modules: list[str] = [
        root_product_module(start, degree, "RawLeftData")]
    modules.extend(
        root_product_right_module(start, degree, right)
        for right in range(len(plan.right_chunks)))
    for left, row in enumerate(plan.pair_chunks):
        for right in range(len(row)):
            modules.extend([
                root_product_pair_module(
                    start, degree, left, right, "Data"),
                root_product_pair_module(
                    start, degree, left, right, "Certificate"),
            ])
    modules.extend([
        root_product_module(start, degree, "RawLeftSplitCertificate"),
        root_product_module(start, degree, "RawRightSplitCertificate"),
    ])
    modules.extend(
        root_product_module(start, degree, f"RawLeft{left}Certificate")
        for left in range(len(plan.theta_terms)))
    modules.extend([
        root_product_module(start, degree, "NormalizeRawData"),
        root_product_module(start, degree, "NormalizeRawCertificate"),
    ])
    for coordinate, buckets, _ in plan.radix_stages:
        modules.extend(
            root_product_radix_bucket_module(
                start, degree, coordinate, bucket)
            for bucket in range(len(buckets)))
        modules.extend([
            root_product_module(
                start, degree, f"NormalizeRadix{coordinate}BucketsData"),
            root_product_module(
                start, degree, f"NormalizeRadix{coordinate}Data"),
            root_product_module(
                start, degree,
                f"NormalizeRadix{coordinate}BucketizeCertificate"),
            root_product_module(
                start, degree,
                f"NormalizeRadix{coordinate}FlattenCertificate"),
            root_product_module(
                start, degree, f"NormalizeRadix{coordinate}Certificate"),
        ])
    modules.extend([
        root_product_module(start, degree, "NormalizeCombineCertificate"),
        root_product_module(start, degree, "Certificate"),
    ])
    expected_count = EXPECTED_ROOT_PRODUCT_MODULE_COUNTS[(start, degree)]
    if len(modules) != expected_count or len(set(modules)) != len(modules):
        raise RuntimeError(
            f"root product ({start}, {degree}) must own exactly "
            f"{expected_count} distinct modules, got {len(modules)}")
    return tuple(modules)


def expected_root_modules() -> tuple[str, ...]:
    """All and only the generated modules owned by root-only generation."""
    modules: list[str] = [
        ROOT_NORMALIZE_SUPPORT_MODULE,
        f"{PREFIX}RootThetaData",
        f"{PREFIX}RootThetaCertificate",
        f"{PREFIX}RootStateData",
    ]
    sharded = set(sharded_root_product_keys())
    for start, degree in root_state_keys():
        if (start, degree) in sharded:
            modules.extend(root_product_shard_modules(
                root_product_shard_plan(start, degree)))
        modules.append(root_state_certificate_module(start, degree))
    modules.extend(
        f"{PREFIX}Root{index}Final" for index in range(4))
    modules.append(f"{PREFIX}s")
    if (len(modules) != EXPECTED_ROOT_MODULE_COUNT or
            len(set(modules)) != len(modules)):
        raise RuntimeError(
            f"root closure must contain exactly {EXPECTED_ROOT_MODULE_COUNT} "
            f"distinct modules, got {len(modules)}")
    return tuple(modules)


def write_root_normalize_support(
        emit: ModuleEmitter | None = None) -> str:
    """Emit root-local structural list lemmas without table dependencies."""
    if emit is None:
        emit = write_module
    emit(
        ROOT_NORMALIZE_SUPPORT_MODULE,
        ["ComputableDummitCoefficientsCore"],
        [
            f"theorem {ROOT_RAW_MUL_APPEND_LEFT_CERTIFICATE} "
            "(p r q : SparsePolynomial) :\n"
            "    SparsePolynomial.rawMul (p ++ r) q =\n"
            "      SparsePolynomial.rawMul p q ++\n"
            "        SparsePolynomial.rawMul r q := by\n"
            "  induction p with\n"
            "  | nil => rfl\n"
            "  | cons t p ih =>\n"
            "      change q.map (SparseTerm.mul t) ++\n"
            "          SparsePolynomial.rawMul (p ++ r) q =\n"
            "        (q.map (SparseTerm.mul t) ++\n"
            "          SparsePolynomial.rawMul p q) ++\n"
            "            SparsePolynomial.rawMul r q\n"
            "      rw [ih, List.append_assoc]",
            f"theorem {ROOT_RAW_MUL_SINGLETON_APPEND_RIGHT_CERTIFICATE} "
            "(t : SparseTerm) (q r : SparsePolynomial) :\n"
            "    SparsePolynomial.rawMul [t] (q ++ r) =\n"
            "      SparsePolynomial.rawMul [t] q ++\n"
            "        SparsePolynomial.rawMul [t] r := by\n"
            "  simp [SparsePolynomial.rawMul, List.map_append]",
            f"theorem {ROOT_FLATTEN_BUCKETS_APPEND_CERTIFICATE} "
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
            "      rw [ih, List.append_assoc]",
            f"theorem {ROOT_FLATTEN_BUCKETS_SINGLETON_CERTIFICATE} "
            "(p : SparsePolynomial) :\n"
            "    SparsePolynomial.flattenBuckets [p] = p := by\n"
            "  simp [SparsePolynomial.flattenBuckets]",
        ])
    return ROOT_NORMALIZE_SUPPORT_MODULE


def write_root_product_shards(
        plan: RootProductShardPlan, state_data: str,
        theta_certificate: str,
        emit: ModuleEmitter | None = None) -> str:
    """Emit one bounded raw/radix/combine trace for a root product."""
    validate_root_product_shard_plan(plan)
    if emit is None:
        emit = write_module
    start, degree = plan.start, plan.degree
    child_normal = root_state_normal(start + 1, degree - 1)
    product_normal = root_state_product(start, degree)

    left_data = root_product_module(start, degree, "RawLeftData")
    left_normals = [
        root_product_left_normal(start, degree, left)
        for left in range(len(plan.theta_terms))
    ]
    emit(
        left_data,
        ["ComputableDummitCoefficientsCore"],
        [lean_term_list(name, [term])
         for name, term in zip(left_normals, plan.theta_terms)])

    right_modules: list[str] = []
    right_normals: list[str] = []
    for right, terms in enumerate(plan.right_chunks):
        module = root_product_right_module(start, degree, right)
        normal = root_product_right_normal(start, degree, right)
        emit(module, ["ComputableDummitCoefficientsCore"], [
            lean_term_list(normal, terms),
        ])
        right_modules.append(module)
        right_normals.append(normal)

    pair_modules: list[list[str]] = []
    pair_data_modules: list[str] = []
    pair_normals: list[list[str]] = []
    pair_certificates: list[list[str]] = []
    for left, row in enumerate(plan.pair_chunks):
        row_modules: list[str] = []
        row_normals: list[str] = []
        row_certificates: list[str] = []
        for right, terms in enumerate(row):
            data_module = root_product_pair_module(
                start, degree, left, right, "Data")
            certificate_module = root_product_pair_module(
                start, degree, left, right, "Certificate")
            normal = root_product_pair_normal(
                start, degree, left, right)
            certificate = root_product_pair_certificate(
                start, degree, left, right)
            emit(data_module, ["ComputableDummitCoefficientsCore"], [
                lean_term_list(normal, terms),
            ])
            emit(certificate_module,
                 [left_data, right_modules[right], data_module], [
                decide_theorem(
                    certificate,
                    f"SparsePolynomial.rawMul {left_normals[left]} "
                    f"{right_normals[right]} = {normal}"),
            ])
            pair_data_modules.append(data_module)
            row_modules.append(certificate_module)
            row_normals.append(normal)
            row_certificates.append(certificate)
        pair_modules.append(row_modules)
        pair_normals.append(row_normals)
        pair_certificates.append(row_certificates)

    left_split_module = root_product_module(
        start, degree, "RawLeftSplitCertificate")
    left_split_certificate = root_product_aux_certificate(
        start, degree, "raw_left_split")
    emit(left_split_module, [theta_certificate, left_data], [
        decide_theorem(
            left_split_certificate,
            f"theta{start}Normal = {root_nested_append(left_normals)}"),
    ])

    right_split_module = root_product_module(
        start, degree, "RawRightSplitCertificate")
    right_split_certificate = root_product_aux_certificate(
        start, degree, "raw_right_split")
    emit(right_split_module, [state_data, *right_modules], [
        decide_theorem(
            right_split_certificate,
            f"{child_normal} = {root_nested_append(right_normals)}"),
    ])

    row_certificate_modules: list[str] = []
    row_certificate_names: list[str] = []
    row_normal_expressions: list[str] = []
    right_append_rewrites = [
        ROOT_RAW_MUL_SINGLETON_APPEND_RIGHT_CERTIFICATE
    ] * (len(right_normals) - 1)
    for left, term in enumerate(plan.theta_terms):
        module = root_product_module(
            start, degree, f"RawLeft{left}Certificate")
        certificate = root_product_aux_certificate(
            start, degree, f"raw_left{left}")
        row_expression = root_nested_append(pair_normals[left])
        rewrites = right_append_rewrites + pair_certificates[left]
        emit(
            module,
            [ROOT_NORMALIZE_SUPPORT_MODULE, right_split_module,
             *pair_modules[left]],
            [f"theorem {certificate} :\n"
             f"    SparsePolynomial.rawMul {left_normals[left]} "
             f"{child_normal} = {row_expression} := by\n"
             f"  rw [{right_split_certificate}]\n"
             "  change SparsePolynomial.rawMul "
             f"[{lean_term(term)}] {root_nested_append(right_normals)} =\n"
             f"    {row_expression}\n"
             f"  rw [{', '.join(rewrites)}]"])
        row_certificate_modules.append(module)
        row_certificate_names.append(certificate)
        row_normal_expressions.append(row_expression)

    raw_data = root_product_module(start, degree, "NormalizeRawData")
    raw_normal = root_product_normal(start, degree, "NormalizeRaw")
    raw_expression = root_nested_append(row_normal_expressions)
    emit(raw_data, pair_data_modules, [
        f"def {raw_normal} : SparsePolynomial :=\n"
        f"  {raw_expression}",
    ])

    raw_certificate_module = root_product_module(
        start, degree, "NormalizeRawCertificate")
    raw_certificate = root_product_aux_certificate(
        start, degree, "normalize_raw")
    left_append_rewrites = [ROOT_RAW_MUL_APPEND_LEFT_CERTIFICATE] * \
        (len(left_normals) - 1)
    emit(
        raw_certificate_module,
        [raw_data, left_split_module, ROOT_NORMALIZE_SUPPORT_MODULE,
         *row_certificate_modules],
        [f"theorem {raw_certificate} :\n"
         f"    SparsePolynomial.rawMul theta{start}Normal "
         f"{child_normal} = {raw_normal} := by\n"
         f"  rw [{left_split_certificate}]\n"
         "  change SparsePolynomial.rawMul "
         f"{root_nested_append(left_normals)} {child_normal} =\n"
         f"    {raw_expression}\n"
         f"  rw [{', '.join(left_append_rewrites + row_certificate_names)}]"])

    previous_data = raw_data
    previous_normal = raw_normal
    stage_certificate_modules: list[str] = [raw_certificate_module]
    stage_certificates: list[str] = [raw_certificate]
    for coordinate, buckets, _ in plan.radix_stages:
        bucket_modules: list[str] = []
        bucket_normals: list[str] = []
        for bucket, terms in enumerate(buckets):
            module = root_product_radix_bucket_module(
                start, degree, coordinate, bucket)
            normal = root_product_radix_bucket_normal(
                start, degree, coordinate, bucket)
            emit(module, ["ComputableDummitCoefficientsCore"], [
                lean_term_list(normal, terms),
            ])
            bucket_modules.append(module)
            bucket_normals.append(normal)

        bucket_list_expression = root_nested_append(
            [f"[{normal}]" for normal in bucket_normals])
        flattened_expression = root_nested_append(bucket_normals)
        buckets_data = root_product_module(
            start, degree, f"NormalizeRadix{coordinate}BucketsData")
        buckets_normal = root_product_normal(
            start, degree, f"NormalizeRadix{coordinate}Buckets")
        emit(buckets_data, bucket_modules, [
            f"def {buckets_normal} : List SparsePolynomial :=\n"
            f"  {bucket_list_expression}",
        ])

        stage_data = root_product_module(
            start, degree, f"NormalizeRadix{coordinate}Data")
        stage_normal = root_product_normal(
            start, degree, f"NormalizeRadix{coordinate}")
        emit(stage_data, bucket_modules, [
            f"def {stage_normal} : SparsePolynomial :=\n"
            f"  {flattened_expression}",
        ])

        bucketize_module = root_product_module(
            start, degree,
            f"NormalizeRadix{coordinate}BucketizeCertificate")
        bucketize_certificate = root_product_aux_certificate(
            start, degree, f"normalize_radix{coordinate}_bucketize")
        emit(bucketize_module, [previous_data, buckets_data], [
            decide_theorem(
                bucketize_certificate,
                "SparsePolynomial.bucketize "
                f"(fun t ↦ t.powers.p{coordinate}) {previous_normal} = "
                f"{buckets_normal}"),
        ])

        flatten_module = root_product_module(
            start, degree,
            f"NormalizeRadix{coordinate}FlattenCertificate")
        flatten_certificate = root_product_aux_certificate(
            start, degree, f"normalize_radix{coordinate}_flatten")
        flatten_rewrites = [ROOT_FLATTEN_BUCKETS_APPEND_CERTIFICATE] * \
            (len(bucket_normals) - 1)
        flatten_rewrites.extend(
            [ROOT_FLATTEN_BUCKETS_SINGLETON_CERTIFICATE] *
            len(bucket_normals))
        emit(
            flatten_module,
            [ROOT_NORMALIZE_SUPPORT_MODULE, buckets_data, stage_data],
            [f"theorem {flatten_certificate} :\n"
             "    SparsePolynomial.flattenBuckets "
             f"{buckets_normal} = {stage_normal} := by\n"
             "  change SparsePolynomial.flattenBuckets "
             f"{bucket_list_expression} =\n"
             f"    {flattened_expression}\n"
             f"  rw [{', '.join(flatten_rewrites)}]"])

        certificate_module = root_product_module(
            start, degree, f"NormalizeRadix{coordinate}Certificate")
        certificate = root_product_aux_certificate(
            start, degree, f"normalize_radix{coordinate}")
        emit(certificate_module, [bucketize_module, flatten_module], [
            f"theorem {certificate} :\n"
            "    SparsePolynomial.radixPass "
            f"(fun t ↦ t.powers.p{coordinate}) {previous_normal} = "
            f"{stage_normal} := by\n"
            "  change SparsePolynomial.flattenBuckets\n"
            "    (SparsePolynomial.bucketize "
            f"(fun t ↦ t.powers.p{coordinate}) {previous_normal}) = _\n"
            f"  rw [{bucketize_certificate}, {flatten_certificate}]",
        ])
        stage_certificate_modules.append(certificate_module)
        stage_certificates.append(certificate)
        previous_data = stage_data
        previous_normal = stage_normal

    combine_module = root_product_module(
        start, degree, "NormalizeCombineCertificate")
    combine_certificate = root_product_aux_certificate(
        start, degree, "normalize_combine")
    emit(combine_module, [state_data, previous_data], [
        decide_theorem(
            combine_certificate,
            f"SparsePolynomial.combine {previous_normal} = {product_normal}"),
    ])
    stage_certificate_modules.append(combine_module)
    stage_certificates.append(combine_certificate)

    source = (f"SparsePolynomial.rawMul theta{start}Normal "
              f"{child_normal}")
    for coordinate in reversed(range(5)):
        source = ("SparsePolynomial.radixPass "
                  f"(fun t ↦ t.powers.p{coordinate}) ({source})")
    source = f"SparsePolynomial.combine ({source})"
    endpoint_module = root_product_module(start, degree, "Certificate")
    emit(endpoint_module, stage_certificate_modules, [
        f"theorem {root_state_product_certificate(start, degree)} :\n"
        f"    SparsePolynomial.mul theta{start}Normal {child_normal} = "
        f"{product_normal} := by\n"
        f"  change {source} = {product_normal}\n"
        f"  rw [{', '.join(stage_certificates)}]",
    ])
    return endpoint_module


def write_root_data(
        emit: ModuleEmitter | None = None) -> tuple[str, str]:
    if emit is None:
        emit = write_module
    theta_data = f"{PREFIX}RootThetaData"
    theta_certificate = f"{PREFIX}RootThetaCertificate"
    theta_declarations = [
        lean_polynomial(f"theta{index}Normal", THETAS[index])
        for index in range(6)
    ]
    emit(theta_data, ["ComputableDummitCoefficientsCore"],
         theta_declarations)
    emit(theta_certificate, [theta_data], [
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
    emit(state_data, [theta_certificate], declarations)
    return theta_certificate, state_data


def write_root_state_certificates(theta_certificate: str,
                                  state_data: str,
                                  emit: ModuleEmitter | None = None) -> None:
    if emit is None:
        emit = write_module
    sharded = set(sharded_root_product_keys())
    for start, degree in root_state_keys():
        # The four large public coefficient certificates begin at
        # (start, degree) = (0, 3), ..., (0, 6).  Each recurrence step
        # either preserves or lowers the degree by one, so these are the
        # only unreachable low-degree states in the dependency closure.
        module = root_state_certificate_module(start, degree)
        normal = root_state_normal(start, degree)
        statement = (
            f"SparsePolynomial.esymm {theta_suffix_expression(start)} "
            f"{degree} = {normal}")
        if start == 6 or degree == 0:
            emit(module, [state_data], [
                decide_theorem(root_state_certificate(start, degree),
                               statement, depth=100000),
            ])
            continue
        high_module = root_state_certificate_module(start + 1, degree)
        low_module = root_state_certificate_module(start + 1, degree - 1)
        product = root_state_product(start, degree)
        product_certificate = root_state_product_certificate(start, degree)
        merge_certificate = (
            f"root_state{start}_degree{degree}_merge_certificate")
        imports = [state_data, theta_certificate, high_module, low_module]
        declarations: list[str] = []
        if (start, degree) in sharded:
            imports.append(write_root_product_shards(
                root_product_shard_plan(start, degree), state_data,
                theta_certificate, emit))
        else:
            declarations.append(decide_theorem(
                product_certificate,
                f"SparsePolynomial.mul theta{start}Normal "
                f"{root_state_normal(start + 1, degree - 1)} = {product}"))
        declarations.extend([
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
        ])
        emit(module, imports, declarations)


def write_root_final(index: int, table_final: str,
                     emit: ModuleEmitter | None = None) -> str:
    if emit is None:
        emit = write_module
    degree = 6 - index
    sign = -1 if degree % 2 else 1
    word = table_word(index)
    module = f"{PREFIX}Root{index}Final"
    candidate = f"rootCoefficient{index}Candidate"
    final_certificate = f"root_coefficient_{word}_final_certificate"
    source_certificate = f"sparseRootCoefficient_{word}_certificate"
    common = table_tail_normal(index, 0)
    emit(module,
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


def emit_root_closure(table_finals: list[str] | tuple[str, ...],
                      emit: ModuleEmitter | None = None) -> None:
    """Emit the shared root closure without generating any table modules."""
    expected_table_finals = tuple(
        root_table_final_module(index) for index in range(4))
    if tuple(table_finals) != expected_table_finals:
        raise RuntimeError(
            "root closure requires the four canonical table-final imports")
    if emit is None:
        emit = write_module
    write_root_normalize_support(emit)
    theta_certificate, state_data = write_root_data(emit)
    write_root_state_certificates(theta_certificate, state_data, emit)
    root_finals = [
        write_root_final(index, table_finals[index], emit)
        for index in range(4)
    ]
    emit(f"{PREFIX}s", root_finals, [])


def render_root_closure() -> tuple[dict[str, str],
                                   dict[str, tuple[str, ...]]]:
    """Render and validate the exact root closure entirely in memory."""
    rendered: dict[str, str] = {}
    imports_by_module: dict[str, tuple[str, ...]] = {}

    def collect(name: str, imports: list[str], declarations: list[str]) -> None:
        if name in rendered:
            raise RuntimeError(f"duplicate generated root module: {name}")
        rendered[name] = module_text(imports, declarations)
        imports_by_module[name] = tuple(imports)

    emit_root_closure(
        tuple(root_table_final_module(index) for index in range(4)), collect)
    validate_root_closure(rendered, imports_by_module)
    return rendered, imports_by_module


def expected_root_key_declarations(
        ) -> dict[str, tuple[tuple[str, str], ...]]:
    """Exact declarations for the root closure's public/support modules."""
    declarations: dict[str, tuple[tuple[str, str], ...]] = {
        ROOT_NORMALIZE_SUPPORT_MODULE: tuple(
            ("theorem", name) for name in (
                ROOT_RAW_MUL_APPEND_LEFT_CERTIFICATE,
                ROOT_RAW_MUL_SINGLETON_APPEND_RIGHT_CERTIFICATE,
                ROOT_FLATTEN_BUCKETS_APPEND_CERTIFICATE,
                ROOT_FLATTEN_BUCKETS_SINGLETON_CERTIFICATE,
            )
        ),
        f"{PREFIX}RootThetaData": tuple(
            ("def", f"theta{index}Normal") for index in range(6)),
        f"{PREFIX}RootThetaCertificate": tuple(
            ("theorem", f"thetaPolynomial_{index}_certificate")
            for index in range(6)),
        f"{PREFIX}RootStateData": tuple(
            ("def", declaration)
            for start in reversed(range(7))
            for degree in range(7)
            for declaration in (
                (root_state_normal(start, degree),
                 root_state_product(start, degree))
                if start < 6 and degree > 0
                else (root_state_normal(start, degree),)
            )
        ),
        f"{PREFIX}s": (),
    }
    sharded = set(sharded_root_product_keys())
    for start, degree in root_state_keys():
        names: list[str] = []
        if start < 6 and degree > 0:
            if (start, degree) not in sharded:
                names.append(root_state_product_certificate(start, degree))
            names.append(
                f"root_state{start}_degree{degree}_merge_certificate")
        names.append(root_state_certificate(start, degree))
        declarations[root_state_certificate_module(start, degree)] = \
            tuple(("theorem", name) for name in names)
    for start, degree in sharded:
        declarations[root_product_module(start, degree, "Certificate")] = (
            ("theorem", root_state_product_certificate(start, degree)),)
    for index in range(4):
        word = table_word(index)
        declarations[f"{PREFIX}Root{index}Final"] = (
            ("def", f"rootCoefficient{index}Candidate"),
            ("theorem", f"root_coefficient_{word}_final_certificate"),
            ("theorem", f"sparseRootCoefficient_{word}_certificate"),
        )
    return declarations


def root_module_declarations(
        module: str, payload: str) -> tuple[tuple[str, str], ...]:
    """Validate one rendered root module's trust envelope and declarations."""
    # Root rendering deliberately emits neither comments nor string literals.
    # Reject those forms instead of letting a textual heartbeat directive in
    # non-code lexical context satisfy this fail-closed validation.
    if re.search(r'--|/-|-/|"', payload):
        raise RuntimeError(
            f"root module {module} contains unsupported comments or strings")
    heartbeat_mentions = tuple(
        match.start() for match in re.finditer(r"\bmaxHeartbeats\b", payload))
    heartbeat_pattern = re.compile(
        r"(?m)^[ \t]*set_option[ \t]+(maxHeartbeats)[ \t]+"
        r"([0-9](?:_?[0-9])*)(?:[ \t]+in)?[ \t]*$")
    heartbeat_matches = tuple(heartbeat_pattern.finditer(payload))
    parsed_mentions = tuple(match.start(1) for match in heartbeat_matches)
    heartbeats = tuple(
        int(match.group(2).replace("_", ""))
        for match in heartbeat_matches)
    if (not heartbeats or heartbeat_mentions != parsed_mentions or
            any(value <= 0 or value > 20000000 for value in heartbeats)):
        raise RuntimeError(
            f"root module {module} lacks a finite heartbeat bound")
    forbidden = re.compile(
        r"\b(?:sorry|admit|axiom|constant|unsafe|partial|native_decide|"
        r"sorryAx|ofReduceBool|implemented_by)\b")
    if forbidden.search(payload):
        raise RuntimeError(f"untrusted root proof text in {module}")
    declarations = tuple(re.findall(
        r"(?m)^(def|theorem)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
        payload))
    declaration_names = tuple(name for _, name in declarations)
    if len(declaration_names) != len(set(declaration_names)):
        raise RuntimeError(
            f"duplicate declarations in generated root module {module}")
    if module != f"{PREFIX}s" and not declarations:
        raise RuntimeError(
            f"generated root module {module} has no declaration")
    return declarations


def validate_root_rendered_text(rendered: dict[str, str]) -> None:
    """Fail closed on root proof trust and stable public/support names."""
    declared_by_module = {
        module: root_module_declarations(module, payload)
        for module, payload in rendered.items()
    }
    expected_key_declarations = expected_root_key_declarations()
    for module, expected in expected_key_declarations.items():
        if declared_by_module.get(module) != expected:
            raise RuntimeError(
                f"generated root declarations changed in {module}")
    all_declaration_names = [
        name
        for declarations in declared_by_module.values()
        for _, name in declarations
    ]
    if len(all_declaration_names) != len(set(all_declaration_names)):
        raise RuntimeError("generated root declarations are not unique")
    declared = set(all_declaration_names)
    undeclared_root_names = sorted({
        name
        for payload in rendered.values()
        for name in re.findall(
            r"\b(?:root_[A-Za-z0-9_]+|"
            r"thetaPolynomial_[A-Za-z0-9_]*)\b", payload)
        if name not in declared
    })
    if undeclared_root_names:
        raise RuntimeError(
            "rendered root text references undeclared certificates: "
            + ", ".join(undeclared_root_names))


def validate_root_closure(
        rendered: dict[str, str],
        imports_by_module: dict[str, tuple[str, ...]]) -> None:
    """Fail closed on a malformed root module set or import graph."""
    expected = set(expected_root_modules())
    if set(rendered) != expected or set(imports_by_module) != expected:
        raise RuntimeError("rendered root module set does not match its owner set")

    allowed_external = {
        "ComputableDummitCoefficientsCore",
        *(root_table_final_module(index) for index in range(4)),
    }
    external = {
        dependency
        for imports in imports_by_module.values()
        for dependency in imports
        if dependency not in expected
    }
    if external != allowed_external:
        raise RuntimeError(
            "unexpected root external imports: "
            + ", ".join(sorted(external ^ allowed_external)))
    duplicate_imports = sorted(
        module for module, imports in imports_by_module.items()
        if len(imports) != len(set(imports)))
    if duplicate_imports:
        raise RuntimeError(
            "duplicate generated root imports: "
            + ", ".join(duplicate_imports))

    visited: set[str] = set()
    active: set[str] = set()

    def visit(module: str) -> None:
        if module in active:
            raise RuntimeError(f"cycle in generated root imports at {module}")
        if module in visited:
            return
        active.add(module)
        for dependency in imports_by_module[module]:
            if dependency in expected:
                visit(dependency)
        active.remove(module)
        visited.add(module)

    aggregate = f"{PREFIX}s"
    visit(aggregate)
    if visited != expected:
        unreachable = ", ".join(sorted(expected - visited))
        raise RuntimeError(
            f"generated root modules unreachable from aggregate: {unreachable}")
    validate_root_rendered_text(rendered)


def root_closure_digest(rendered: dict[str, str]) -> str:
    """A stable digest over module names and exact generated bytes."""
    digest = hashlib.sha256()
    for module in sorted(rendered):
        digest.update(module.encode("utf-8"))
        digest.update(b"\0")
        digest.update(rendered[module].encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest()


def existing_owned_root_paths(lean_dir: Path = LEAN_DIR) -> set[Path]:
    """Root sources owned by this mode; table sources are deliberately out."""
    return {
        *lean_dir.glob(f"{PREFIX}Root*.lean"),
        *lean_dir.glob(f"{PREFIX}s.lean"),
    }


def existing_owned_root_modules(lean_dir: Path = LEAN_DIR) -> set[str]:
    """Validate and return existing generator-owned root module names."""
    paths = existing_owned_root_paths(lean_dir)
    invalid = sorted(
        str(path) for path in paths
        if path.is_symlink() or not path.is_file()
    )
    for module in expected_root_modules():
        path = lean_dir / f"{module}.lean"
        if path.is_symlink():
            invalid.append(str(path))
    if invalid:
        raise RuntimeError(
            "refusing non-regular generated root paths:\n  "
            + "\n  ".join(sorted(set(invalid))))
    return {path.stem for path in paths}


def required_root_input_paths(lean_dir: Path = LEAN_DIR) -> tuple[Path, ...]:
    """External sources required before checking or writing root modules."""
    return (
        lean_dir / "ComputableDummitCoefficientsCore.lean",
        *(lean_dir / f"{root_table_final_module(index)}.lean"
          for index in range(4)),
    )


def validate_required_root_inputs(lean_dir: Path = LEAN_DIR) -> None:
    """Require all external root inputs to be regular, nonsymlink files."""
    invalid = [
        path for path in required_root_input_paths(lean_dir)
        if path.is_symlink() or not path.is_file()
    ]
    if invalid:
        raise RuntimeError(
            "missing or non-regular required root inputs:\n  "
            + "\n  ".join(str(path) for path in invalid))


def root_closure_differences(
        rendered: dict[str, str], lean_dir: Path = LEAN_DIR
        ) -> tuple[list[str], list[str], list[str]]:
    """Return missing, unexpected, and byte-stale root module names."""
    expected = set(rendered)
    existing = existing_owned_root_modules(lean_dir)
    missing = sorted(expected - existing)
    unexpected = sorted(existing - expected)
    stale = sorted(
        module for module in expected & existing
        if (lean_dir / f"{module}.lean").read_bytes()
        != rendered[module].encode("utf-8")
    )
    return missing, unexpected, stale


def format_root_closure_differences(
        missing: list[str], unexpected: list[str], stale: list[str]) -> str:
    lines = ["root closure check failed"]
    for label, modules in (
            ("missing", missing),
            ("unexpected", unexpected),
            ("stale-content", stale)):
        if modules:
            lines.append(f"  {label} ({len(modules)}):")
            lines.extend(f"    {module}.lean" for module in modules)
    return "\n".join(lines)


def check_root_closure(lean_dir: Path = LEAN_DIR) -> str:
    """Check the root closure without writing generated sources."""
    validate_required_root_inputs(lean_dir)
    rendered, _ = render_root_closure()
    missing, unexpected, stale = root_closure_differences(rendered, lean_dir)
    if missing or unexpected or stale:
        raise RuntimeError(
            format_root_closure_differences(missing, unexpected, stale))
    return root_closure_digest(rendered)


def write_root_closure(lean_dir: Path = LEAN_DIR) -> str:
    """Write only the expected root sources, refusing to delete orphans."""
    validate_required_root_inputs(lean_dir)
    rendered, _ = render_root_closure()
    _, unexpected, _ = root_closure_differences(rendered, lean_dir)
    if unexpected:
        raise RuntimeError(format_root_closure_differences([], unexpected, []))
    for module in expected_root_modules():
        path = lean_dir / f"{module}.lean"
        payload = rendered[module].encode("utf-8")
        if not path.exists() or path.read_bytes() != payload:
            path.write_bytes(payload)
    return check_root_closure(lean_dir)


def write_all_certificates() -> None:
    rows = parse_table()
    table_finals: list[str] = []
    for index in range(4):
        row = rows[index]
        write_table_term_certificates(index, row)
        row_data, group_count = write_table_row_data(index, row)
        write_table_tail_certificates(index, row, row_data, group_count)
        table_finals.append(write_table_final(index, row, row_data))
    emit_root_closure(table_finals)


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
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--stats", action="store_true")
    modes.add_argument("--write-probe", action="store_true")
    modes.add_argument("--write-all", action="store_true")
    modes.add_argument(
        "--write-term-shards", nargs=2, type=int,
        metavar=("TABLE_INDEX", "TERM_POSITION"),
        help="regenerate one table-term certificate using accumulator shards")
    modes.add_argument(
        "--write-tail-shards", nargs=2, type=int,
        metavar=("TABLE_INDEX", "TAIL_INDEX"),
        help="write one explicitly authorized stagewise tail-merge graph")
    modes.add_argument(
        "--check-tail-shards", nargs=2, type=int,
        metavar=("TABLE_INDEX", "TAIL_INDEX"),
        help="check one explicitly authorized stagewise tail-merge graph")
    modes.add_argument(
        "--write-root", action="store_true",
        help=("write only the exact generated shared root closure "
              f"({EXPECTED_ROOT_MODULE_COUNT} modules)"))
    modes.add_argument(
        "--check-root", action="store_true",
        help="check the exact root closure without writing any source")
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
    if args.write_tail_shards or args.check_tail_shards:
        index, group = (args.write_tail_shards or args.check_tail_shards)
        rows = parse_table()
        if not 0 <= index < 4:
            parser.error("TABLE_INDEX must be between 0 and 3")
        group_count = (len(rows[index]) + TABLE_BLOCK_SIZE - 1) // \
            TABLE_BLOCK_SIZE
        if not 0 <= group < group_count:
            parser.error(
                f"TAIL_INDEX must be between 0 and {group_count - 1} "
                f"for table {index}")
        try:
            require_authorized_tail_shard_target(index, group)
            if args.write_tail_shards:
                digest = write_tail_shard_target(index, group, rows[index])
                action = "written"
            else:
                digest = check_tail_shard_target(index, group, rows[index])
                action = "check passed"
        except (OSError, RuntimeError) as error:
            parser.exit(1, f"{error}\n")
        print(f"table {index} tail {group} shard graph {action}: "
              f"{TAIL_SHARD_MODULE_COUNT} modules, sha256 {digest}")
        return
    if args.write_root:
        try:
            digest = write_root_closure()
        except (OSError, RuntimeError) as error:
            parser.exit(1, f"{error}\n")
        print("root closure written: "
              f"{EXPECTED_ROOT_MODULE_COUNT} modules, sha256 {digest}")
        return
    if args.check_root:
        try:
            digest = check_root_closure()
        except (OSError, RuntimeError) as error:
            parser.exit(1, f"{error}\n")
        print("root closure check passed: "
              f"{EXPECTED_ROOT_MODULE_COUNT} modules, sha256 {digest}")
        return
    if args.write_all:
        write_all_certificates()
        return
    parser.error("generation modes will be added after validating source data")


if __name__ == "__main__":
    main()
