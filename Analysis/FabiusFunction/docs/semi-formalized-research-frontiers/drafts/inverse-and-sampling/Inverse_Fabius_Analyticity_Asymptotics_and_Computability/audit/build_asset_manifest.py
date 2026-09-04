#!/usr/bin/env python3
"""Build and verify the canonical inverse-Fabius reproducibility assets.

The source corpus is read from the exact Git commit recorded in
``audit/SOURCE_REVISION``; later edits or retirement of the source packages
therefore cannot change this audit.  This program copies only reviewed, unique
payloads and writes the exhaustive 88-row disposition ledger.  ``--check`` is
a strict read-only replay after the initial build.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path
from typing import Callable


CANONICAL_ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = CANONICAL_ROOT.parent
SOURCE_REVISION_FILE = CANONICAL_ROOT / "audit/SOURCE_REVISION"
ASSET_ROOT = CANONICAL_ROOT / "assets"
DISPOSITION_CSV = CANONICAL_ROOT / "ASSET_DISPOSITION.csv"
STURM_CERTIFICATE = ASSET_ROOT / "self-sampling/appell_a8_sturm_certificate.txt"
SOURCE_GROUPS = (
    "inverse-asymptotics-and-computability",
    "analyticity-and-elementarity",
)

IAS = "inverse-asymptotics-and-computability"
ANA = "analyticity-and-elementarity"
SAMPLING = f"{IAS}/Inverse_and_Sampling_Frontiers"
SELF = f"{SAMPLING}/assets/Fabius_Dyadic_Self_Sampling_Frontier_Package"
GERMS = f"{SAMPLING}/assets/Fabius_Inverse_Frontier_Report_Source_and_PDF"
ENDPOINT = f"{IAS}/Inverse_Endpoint_All_Orders"
ALL_ORDERS = f"{ENDPOINT}/assets/inverse_fabius_all_orders_package"
WRIGHT = f"{ENDPOINT}/assets/inverse_fabius_asymptotics_package"
COMPLETION = f"{ENDPOINT}/assets/inverse_fabius_asymptotics_report"
COMPUTABILITY = f"{IAS}/Inverse_Fabius_Computability_Report"
NON_ELEMENTARY = f"{ANA}/Non_Elementarity_of_the_Fabius_Function"
ITERATES = f"{ANA}/inverse_fabius_iterates_nowhere_analytic"


@dataclass(frozen=True)
class Entry:
    semantic_class: str
    canonical_destination: str
    disposition: str
    rationale: str
    copy_payload: bool = False
    transform: str = ""


ENTRIES: dict[str, Entry] = {}


DEFAULT_RATIONALE = {
    "reproduction_script": (
        "Unique reproducibility program retained under a semantic namespace."
    ),
    "numeric_data": "Unique exact or high-precision data snapshot retained.",
    "numeric_log": "Unique symbolic or numerical verification log retained.",
    "generated_tex": "Unique machine-generated TeX fragment retained.",
    "figure_raster": "Unique raster figure retained for reproducible comparison.",
    "figure_vector": "Unique vector figure retained for publication use.",
    "provenance_ledger": (
        "Historical checksum or arrival manifest retained as provenance, not "
        "as the live canonical ledger."
    ),
    "claim_audit": "Source-corpus audit retained as historical provenance.",
    "run_metadata": "Unique numerical replay metadata retained.",
}


def add(
    source: str,
    semantic_class: str,
    canonical_destination: str,
    disposition: str,
    rationale: str,
    *,
    copy_payload: bool = False,
    transform: str = "",
) -> None:
    if source in ENTRIES:
        raise ValueError(f"duplicate disposition entry: {source}")
    ENTRIES[source] = Entry(
        semantic_class,
        canonical_destination,
        disposition,
        rationale,
        copy_payload,
        transform,
    )


def retain(
    source: str,
    destination: str,
    semantic_class: str,
    rationale: str | None = None,
    *,
    disposition: str = "retained_copy",
    transform: str = "",
) -> None:
    add(
        source,
        semantic_class,
        destination,
        disposition,
        rationale or DEFAULT_RATIONALE[semantic_class],
        copy_payload=True,
        transform=transform,
    )


def omit(
    source: str,
    semantic_class: str,
    disposition: str,
    rationale: str,
    destination: str = "",
) -> None:
    add(source, semantic_class, destination, disposition, rationale)


# Subgroup catalogs and master documents.
omit(
    f"{IAS}/README.md",
    "subgroup_documentation",
    "merged_into_canonical_documentation",
    "The subgroup catalog is replaced by the canonical package documentation.",
    "README.md",
)
omit(
    f"{ANA}/README.md",
    "subgroup_documentation",
    "merged_into_canonical_documentation",
    "The subgroup catalog is replaced by the canonical package documentation.",
    "README.md",
)

omit(
    f"{SAMPLING}/Inverse_and_Sampling_Frontiers.tex",
    "master_source",
    "absorbed_into_canonical_text",
    "Result-level content is tracked by the theorem concordance and canonical chapters.",
    "chapters/03_inverse_germs_and_deconvolution.tex; "
    "chapters/04_endpoint_all_orders.tex; chapters/05_dyadic_self_sampling.tex",
)
omit(
    f"{SAMPLING}/Inverse_and_Sampling_Frontiers.pdf",
    "historical_render",
    "retire_after_canonical_publication",
    "The retained PDF predates the current source and is superseded by the canonical PDF.",
)
omit(
    f"{ENDPOINT}/Inverse_Endpoint_All_Orders.tex",
    "master_source",
    "absorbed_into_canonical_text",
    "Result-level content is tracked by the theorem concordance and endpoint chapter.",
    "chapters/04_endpoint_all_orders.tex",
)
omit(
    f"{ENDPOINT}/Inverse_Endpoint_All_Orders.pdf",
    "historical_render",
    "retire_after_canonical_publication",
    "The stale render contains Type-3 plot fonts and is superseded by the canonical PDF.",
)
omit(
    f"{COMPUTABILITY}/inverse_fabius_computability.tex",
    "master_source",
    "absorbed_into_canonical_text",
    "Result-level content is tracked by the theorem concordance and computability chapter.",
    "chapters/06_computability.tex",
)
omit(
    f"{COMPUTABILITY}/inverse_fabius_computability.pdf",
    "historical_render",
    "retire_after_canonical_publication",
    "The retained PDF is not synchronized with the current source.",
)
omit(
    f"{NON_ELEMENTARY}/Non_Elementarity_of_the_Fabius_Function.tex",
    "master_source",
    "absorbed_into_canonical_text",
    "Result-level content is tracked by the theorem concordance and analyticity chapter.",
    "chapters/01_analyticity_and_elementarity.tex",
)
omit(
    f"{NON_ELEMENTARY}/Non_Elementarity_of_the_Fabius_Function.pdf",
    "historical_render",
    "retire_after_canonical_publication",
    "The synchronized source PDF is superseded by the canonical integrated render.",
)
omit(
    f"{ITERATES}/inverse_fabius_iterates_nowhere_analytic.tex",
    "master_source",
    "absorbed_into_canonical_text",
    "Unique inverse-facing content is tracked by the concordance and iterate chapter.",
    "chapters/02_inverse_iterates.tex",
)
omit(
    f"{ITERATES}/inverse_fabius_iterates_nowhere_analytic.pdf",
    "historical_render",
    "retire_after_canonical_publication",
    "The retained PDF is not synchronized with the current source.",
)

# Finite self-sampling lane.
retain(
    f"{SELF}/appell_polynomials.tex",
    "assets/self-sampling/generated/appell_polynomials.tex",
    "generated_tex",
)
retain(
    f"{SELF}/appell_root_certificate.txt",
    "assets/self-sampling/data/appell_root_certificate.txt",
    "numeric_log",
)
retain(
    f"{SELF}/appell_root_counts.csv",
    "assets/self-sampling/data/appell_root_counts.csv",
    "numeric_data",
)
retain(
    f"{SELF}/appell_roots.png",
    "assets/self-sampling/figures/appell_roots.png",
    "figure_raster",
)
retain(
    f"{SELF}/defect_profiles.png",
    "assets/self-sampling/figures/defect_profiles.png",
    "figure_raster",
)
retain(
    f"{SELF}/experiments.py",
    "assets/self-sampling/scripts/experiments.py",
    "reproduction_script",
)
retain(
    f"{SELF}/harmonic_tail_table.tex",
    "assets/self-sampling/generated/harmonic_tail_table.tex",
    "generated_tex",
)
retain(
    f"{SELF}/quadrature_table_display.tex",
    "assets/self-sampling/generated/quadrature_table_display.tex",
    "generated_tex",
    "Decimal display paired with the exact table; both are generated from one script.",
)
retain(
    f"{SELF}/quadrature_table.csv",
    "assets/self-sampling/data/quadrature_table.csv",
    "numeric_data",
)
retain(
    f"{SELF}/quadrature_table.tex",
    "assets/self-sampling/generated/quadrature_table_exact.tex",
    "generated_tex",
    "Exact table paired with the decimal display and common generating script.",
)
retain(
    f"{SELF}/quadrature_weights.png",
    "assets/self-sampling/figures/quadrature_weights.png",
    "figure_raster",
)
omit(
    f"{SELF}/README.txt",
    "package_documentation",
    "merged_into_canonical_reproduction_readme",
    "Commands and status notes are consolidated into the canonical asset README.",
    "assets/README.md",
)
retain(
    f"{SELF}/spectral_check_display.tex",
    "assets/self-sampling/generated/spectral_check_display.tex",
    "generated_tex",
    "Decimal display paired with the exact spectral table and common generating script.",
)
retain(
    f"{SELF}/spectral_check.tex",
    "assets/self-sampling/generated/spectral_check_exact.tex",
    "generated_tex",
    "Exact spectral table paired with its decimal display.",
)

# Finite-prefix inverse-germ lane.
retain(
    f"{GERMS}/generate_data.py",
    "assets/inverse-germs/scripts/generate_data.py",
    "reproduction_script",
    "Unique generator retained with its hard-coded /mnt/data destination replaced by "
    "a portable --output-dir option.",
    disposition="retained_with_portability_patch",
    transform="portable_inverse_germ_output",
)
omit(
    f"{GERMS}/README.txt",
    "package_documentation",
    "merged_into_canonical_reproduction_readme",
    "Commands, dependencies, and status notes are consolidated into the asset README.",
    "assets/README.md",
)
retain(
    f"{GERMS}/SHA256SUMS.txt",
    "assets/provenance/sampling/inverse-frontier-SHA256SUMS.txt",
    "provenance_ledger",
)
retain(
    f"{GERMS}/verify_symbolic_fast.py",
    "assets/inverse-germs/scripts/verify_symbolic_fast.py",
    "reproduction_script",
)
for name, semantic_class in (
    ("constants.txt", "numeric_data"),
    ("endpoint_errors.csv", "numeric_data"),
    ("quarter_quantile_errors.csv", "numeric_data"),
    ("symbolic_verification.txt", "numeric_log"),
):
    retain(
        f"{GERMS}/data/{name}",
        f"assets/inverse-germs/data/{name}",
        semantic_class,
    )
for name in (
    "endpoint_inverse_errors.png",
    "periodic_inverse_phase.png",
    "quarter_quantile_richardson.png",
):
    retain(
        f"{GERMS}/figures/{name}",
        f"assets/inverse-germs/figures/{name}",
        "figure_raster",
    )

# Endpoint all-orders lane.
retain(
    f"{ENDPOINT}/assets/SHA256SUMS-absorbed.txt",
    "assets/provenance/endpoint/SHA256SUMS-absorbed.txt",
    "provenance_ledger",
)
retain(
    f"{ALL_ORDERS}/inverse_fabius_asymptotics.py",
    "assets/endpoint/all-orders/scripts/inverse_fabius_asymptotics.py",
    "reproduction_script",
)
omit(
    f"{ALL_ORDERS}/README.txt",
    "package_documentation",
    "merged_into_canonical_reproduction_readme",
    "Commands and package layout are consolidated into the asset README.",
    "assets/README.md",
)
retain(
    f"{ALL_ORDERS}/SHA256SUMS.txt",
    "assets/provenance/endpoint/all-orders-SHA256SUMS.txt",
    "provenance_ledger",
)
retain(
    f"{ALL_ORDERS}/results/constants.txt",
    "assets/endpoint/all-orders/data/constants.txt",
    "numeric_data",
)
retain(
    f"{ALL_ORDERS}/results/endpoint_error_plot.pdf",
    "assets/endpoint/all-orders/figures/endpoint_error_plot.pdf",
    "figure_vector",
)
retain(
    f"{ALL_ORDERS}/results/endpoint_error_plot.png",
    "assets/endpoint/all-orders/figures/endpoint_error_plot.png",
    "figure_raster",
)
retain(
    f"{ALL_ORDERS}/results/endpoint_errors.csv",
    "assets/endpoint/all-orders/data/endpoint_errors.csv",
    "numeric_data",
)
retain(
    f"{ALL_ORDERS}/results/symbolic_checks.txt",
    "assets/endpoint/all-orders/data/symbolic_checks.txt",
    "numeric_log",
)

# Wright--omega endpoint lane.  Only one source copy of each duplicate PNG is
# migrated; the duplicate source row still receives a complete disposition.
retain(
    f"{WRIGHT}/CORPUS_AUDIT.txt",
    "assets/provenance/endpoint/wright-omega-CORPUS_AUDIT.txt",
    "claim_audit",
)
retain(
    f"{WRIGHT}/inverse_fabius_experiments.py",
    "assets/endpoint/wright-omega/scripts/inverse_fabius_experiments.py",
    "reproduction_script",
)
omit(
    f"{WRIGHT}/README.md",
    "package_documentation",
    "merged_into_canonical_reproduction_readme",
    "Commands and package layout are consolidated into the asset README.",
    "assets/README.md",
)
omit(
    f"{WRIGHT}/requirements.txt",
    "dependency_specification",
    "consolidated_into_dependency_specification",
    "The strongest supplied lower bounds are merged into one canonical requirement set.",
    "assets/requirements.txt",
)
retain(
    f"{WRIGHT}/SHA256SUMS.txt",
    "assets/provenance/endpoint/wright-omega-SHA256SUMS.txt",
    "provenance_ledger",
)
retain(
    f"{WRIGHT}/data/carrier_comparison.png",
    "assets/endpoint/wright-omega/figures/carrier_comparison.png",
    "figure_raster",
)
retain(
    f"{WRIGHT}/data/dyadic_inverse_comparison.csv",
    "assets/endpoint/wright-omega/data/dyadic_inverse_comparison.csv",
    "numeric_data",
)
retain(
    f"{WRIGHT}/data/exact_dyadic_values.txt",
    "assets/endpoint/wright-omega/data/exact_dyadic_values.txt",
    "numeric_data",
)
retain(
    f"{WRIGHT}/data/scaled_residuals.png",
    "assets/endpoint/wright-omega/figures/scaled_residuals.png",
    "figure_raster",
)
retain(
    f"{WRIGHT}/data/symbolic_inverse_coefficients.txt",
    "assets/endpoint/wright-omega/data/symbolic_inverse_coefficients.txt",
    "numeric_log",
)
retain(
    f"{WRIGHT}/figures/carrier_comparison.pdf",
    "assets/endpoint/wright-omega/figures/carrier_comparison.pdf",
    "figure_vector",
)
omit(
    f"{WRIGHT}/figures/carrier_comparison.png",
    "figure_raster",
    "deduplicated_to_retained_payload",
    "Byte-identical to data/carrier_comparison.png; only one canonical copy is kept.",
    "assets/endpoint/wright-omega/figures/carrier_comparison.png",
)
retain(
    f"{WRIGHT}/figures/scaled_residuals.pdf",
    "assets/endpoint/wright-omega/figures/scaled_residuals.pdf",
    "figure_vector",
)
omit(
    f"{WRIGHT}/figures/scaled_residuals.png",
    "figure_raster",
    "deduplicated_to_retained_payload",
    "Byte-identical to data/scaled_residuals.png; only one canonical copy is kept.",
    "assets/endpoint/wright-omega/figures/scaled_residuals.png",
)

# Exact dyadic-completion endpoint lane.
retain(
    f"{COMPLETION}/dyadic_tail_convergence.pdf",
    "assets/endpoint/dyadic-completion/figures/dyadic_tail_convergence.pdf",
    "figure_vector",
)
retain(
    f"{COMPLETION}/generated_coefficients.tex",
    "assets/endpoint/dyadic-completion/generated/generated_coefficients.tex",
    "generated_tex",
)
retain(
    f"{COMPLETION}/inverse_fabius_experiments.py",
    "assets/endpoint/dyadic-completion/scripts/inverse_fabius_experiments.py",
    "reproduction_script",
)
retain(
    f"{COMPLETION}/psi_periodic.pdf",
    "assets/endpoint/dyadic-completion/figures/psi_periodic.pdf",
    "figure_vector",
)
omit(
    f"{COMPLETION}/README.md",
    "package_documentation",
    "merged_into_canonical_reproduction_readme",
    "Commands and package layout are consolidated into the asset README.",
    "assets/README.md",
)
omit(
    f"{COMPLETION}/requirements.txt",
    "dependency_specification",
    "consolidated_into_dependency_specification",
    "The strongest supplied lower bounds are merged into one canonical requirement set.",
    "assets/requirements.txt",
)
retain(
    f"{COMPLETION}/SHA256SUMS",
    "assets/provenance/endpoint/dyadic-completion-SHA256SUMS.txt",
    "provenance_ledger",
)
retain(
    f"{COMPLETION}/verification_output.txt",
    "assets/endpoint/dyadic-completion/data/verification_output.txt",
    "numeric_log",
)

# Computability lane.
retain(
    f"{COMPUTABILITY}/ARRIVAL_SHA256SUMS.txt",
    "assets/provenance/computability/ARRIVAL_SHA256SUMS.txt",
    "provenance_ledger",
)
retain(
    f"{COMPUTABILITY}/inverse_fabius_computability_experiments.py",
    "assets/computability/inverse_fabius_computability_experiments.py",
    "reproduction_script",
)
retain(
    f"{COMPUTABILITY}/numerical_output.txt",
    "assets/computability/numerical_output.txt",
    "numeric_log",
)
omit(
    f"{COMPUTABILITY}/README.txt",
    "package_documentation",
    "merged_into_canonical_documentation",
    "Status, crosswalk, and reproduction notes are consolidated into canonical documentation.",
    "PROVENANCE.md; assets/README.md",
)
omit(
    f"{COMPUTABILITY}/SHA256SUMS.txt",
    "operational_checksum_ledger",
    "not_retained_stale_operational_ledger",
    "The TeX and README rows are stale; the canonical live ledger replaces it.",
)

# The historical package-local ledger is intentionally not copied into the
# canonical tree: SHA256SUMS and SHA256SUMS.* basenames are retired.
omit(
    f"{NON_ELEMENTARY}/SHA256SUMS",
    "provenance_ledger",
    "retired_checksum_ledger",
    "The historical ledger remains recoverable from the pinned source revision.",
)

# Inverse-iterate lane.
retain(
    f"{ITERATES}/MANIFEST.txt",
    "assets/provenance/inverse-iterates/MANIFEST.txt",
    "provenance_ledger",
)
retain(
    f"{ITERATES}/numerical_experiments.py",
    "assets/inverse-iterates/numerical_experiments.py",
    "reproduction_script",
)
omit(
    f"{ITERATES}/README.md",
    "package_documentation",
    "merged_into_canonical_documentation",
    "Status, corrections, and reproduction notes are consolidated into canonical documentation.",
    "PROVENANCE.md; assets/README.md",
)
retain(
    f"{ITERATES}/REPOSITORY_AUDIT.md",
    "assets/provenance/inverse-iterates/REPOSITORY_AUDIT.md",
    "claim_audit",
)
omit(
    f"{ITERATES}/requirements.txt",
    "dependency_specification",
    "consolidated_into_dependency_specification",
    "The dependency names are merged into one canonical requirement set.",
    "assets/requirements.txt",
)
# The arrival ledger remains represented by its pinned-source disposition row,
# but is no longer copied under a retired basename.
omit(
    f"{ITERATES}/SHA256SUMS.arrival.txt",
    "provenance_ledger",
    "retired_checksum_ledger",
    "The historical ledger remains recoverable from the pinned source revision.",
)
omit(
    f"{ITERATES}/SHA256SUMS.txt",
    "operational_checksum_ledger",
    "not_retained_stale_operational_ledger",
    "The source and README rows are stale; the canonical live ledger replaces it.",
)
for name in ("fabius_iterates.png", "spine_comparison.png", "spine_remainder.png"):
    omit(
        f"{ITERATES}/figures/{name}",
        "figure_raster",
        "external_duplicate_not_copied",
        "Byte-identical to the corrected forward-iterate package; that package remains "
        "the canonical owner of the forward figure.",
    )
retain(
    f"{ITERATES}/figures/inverse_taylor_root_diagnostic.png",
    "assets/inverse-iterates/figures/inverse_taylor_root_diagnostic.png",
    "figure_raster",
    "Unique inverse-facing formal-reversion diagnostic retained.",
)
omit(
    f"{ITERATES}/figures/taylor_root_diagnostic.png",
    "figure_raster",
    "not_retained_pending_forward_reconciliation",
    "Forward-facing payload differs from the corrected forward report and must be regenerated "
    "from the chosen forward engine before publication.",
)
retain(
    f"{ITERATES}/numerical_output/numerical_metadata.txt",
    "assets/inverse-iterates/data/numerical_metadata.txt",
    "run_metadata",
)
retain(
    f"{ITERATES}/numerical_output/spine_diagnostic.csv",
    "assets/inverse-iterates/data/spine_diagnostic.csv",
    "numeric_data",
)


TRANSFORMS: dict[str, Callable[[bytes], bytes]] = {}


def portable_inverse_germ_output(payload: bytes) -> bytes:
    text = payload.decode("utf-8")
    import_anchor = "from pathlib import Path\nimport csv\n"
    if text.count(import_anchor) != 1:
        raise ValueError("inverse-germ generator import anchor changed")
    text = text.replace(
        import_anchor,
        "from pathlib import Path\nimport argparse\nimport csv\n",
    )
    root_anchor = (
        "ROOT = Path('/mnt/data/fabius_inverse_frontier')\n"
        "FIG = ROOT / 'figures'\n"
        "DATA = ROOT / 'data'\n"
    )
    if text.count(root_anchor) != 1:
        raise ValueError("inverse-germ generator output anchor changed")
    replacement = (
        "parser = argparse.ArgumentParser(description=__doc__)\n"
        "parser.add_argument(\n"
        "    '--output-dir',\n"
        "    type=Path,\n"
        "    default=Path('reproduced-inverse-germs'),\n"
        "    help='directory for generated data and figures',\n"
        ")\n"
        "arguments = parser.parse_args()\n\n"
        "ROOT = arguments.output_dir\n"
        "FIG = ROOT / 'figures'\n"
        "DATA = ROOT / 'data'\n"
    )
    return text.replace(root_anchor, replacement).encode("utf-8")


TRANSFORMS["portable_inverse_germ_output"] = portable_inverse_germ_output


CSV_FIELDS = (
    "source_path",
    "sha256",
    "size_bytes",
    "semantic_class",
    "canonical_destination",
    "disposition",
    "rationale",
)


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def git_output(repository_root: Path, *arguments: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(repository_root), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise ValueError(
            f"git {' '.join(arguments)} failed with exit code "
            f"{result.returncode}: {detail}"
        )
    return result.stdout


def repository_root() -> Path:
    root = git_output(CANONICAL_ROOT, "rev-parse", "--show-toplevel")
    return Path(root.decode("utf-8").strip()).resolve()


def source_revision(repository_root: Path) -> str:
    revision = SOURCE_REVISION_FILE.read_text(encoding="ascii").strip()
    if len(revision) != 40 or any(
        character not in "0123456789abcdef" for character in revision
    ):
        raise ValueError(
            f"{SOURCE_REVISION_FILE} must contain one full lowercase Git object ID"
        )
    resolved = git_output(
        repository_root, "rev-parse", "--verify", f"{revision}^{{commit}}"
    ).decode("ascii").strip()
    if resolved != revision:
        raise ValueError(
            f"source revision did not resolve to itself: {revision} -> {resolved}"
        )
    return revision


def source_files() -> dict[str, bytes]:
    repository = repository_root()
    revision = source_revision(repository)
    try:
        source_prefix = SOURCE_ROOT.relative_to(repository).as_posix()
    except ValueError as error:
        raise ValueError(
            f"source root is outside the Git repository: {SOURCE_ROOT}"
        ) from error

    group_paths = [f"{source_prefix}/{group}" for group in SOURCE_GROUPS]
    listing = git_output(
        repository,
        "ls-tree",
        "-r",
        "-z",
        "--name-only",
        revision,
        "--",
        *group_paths,
    )
    repository_paths = [
        path.decode("utf-8") for path in listing.split(b"\0") if path
    ]
    relative_prefix = f"{source_prefix}/"
    files: dict[str, bytes] = {}
    for repository_path in repository_paths:
        if not repository_path.startswith(relative_prefix):
            raise ValueError(
                f"Git listed a path outside the source root: {repository_path}"
            )
        relative = repository_path.removeprefix(relative_prefix)
        files[relative] = git_output(
            repository, "show", f"{revision}:{repository_path}"
        )
    return files


def transformed_payload(payload: bytes, entry: Entry) -> bytes:
    if entry.transform:
        payload = TRANSFORMS[entry.transform](payload)
    return payload


def disposition_rows(files: dict[str, bytes]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for source in sorted(files):
        payload = files[source]
        entry = ENTRIES[source]
        rows.append(
            {
                "source_path": source,
                "sha256": sha256_bytes(payload),
                "size_bytes": str(len(payload)),
                "semantic_class": entry.semantic_class,
                "canonical_destination": entry.canonical_destination,
                "disposition": entry.disposition,
                "rationale": entry.rationale,
            }
        )
    return rows


def csv_payload(rows: list[dict[str, str]]) -> bytes:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=CSV_FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


Polynomial = tuple[Fraction, ...]  # coefficients in increasing degree order


def polynomial_trim(coefficients: Polynomial) -> Polynomial:
    end = len(coefficients)
    while end > 1 and coefficients[end - 1] == 0:
        end -= 1
    return coefficients[:end] if end else (Fraction(0),)


def polynomial_derivative(polynomial: Polynomial) -> Polynomial:
    if len(polynomial) == 1:
        return (Fraction(0),)
    return polynomial_trim(
        tuple(Fraction(degree) * polynomial[degree] for degree in range(1, len(polynomial)))
    )


def polynomial_divmod(
    numerator: Polynomial, denominator: Polynomial
) -> tuple[Polynomial, Polynomial]:
    numerator = polynomial_trim(numerator)
    denominator = polynomial_trim(denominator)
    if denominator == (Fraction(0),):
        raise ZeroDivisionError("polynomial division by zero")
    if len(numerator) < len(denominator):
        return (Fraction(0),), numerator
    quotient = [Fraction(0)] * (len(numerator) - len(denominator) + 1)
    remainder = list(numerator)
    while not (len(remainder) == 1 and remainder[0] == 0) and len(remainder) >= len(
        denominator
    ):
        shift = len(remainder) - len(denominator)
        factor = remainder[-1] / denominator[-1]
        quotient[shift] += factor
        for degree, coefficient in enumerate(denominator):
            remainder[degree + shift] -= factor * coefficient
        remainder = list(polynomial_trim(tuple(remainder)))
    return polynomial_trim(tuple(quotient)), polynomial_trim(tuple(remainder))


def polynomial_negate(polynomial: Polynomial) -> Polynomial:
    return tuple(-coefficient for coefficient in polynomial)


def polynomial_scale(polynomial: Polynomial, scale: Fraction) -> Polynomial:
    return polynomial_trim(tuple(scale * coefficient for coefficient in polynomial))


def primitive_integer_form(polynomial: Polynomial) -> tuple[Fraction, Polynomial]:
    denominator = lcm(*(coefficient.denominator for coefficient in polynomial))
    integers = [int(coefficient * denominator) for coefficient in polynomial]
    content = 0
    for coefficient in integers:
        content = gcd(content, abs(coefficient))
    if content == 0:
        raise ValueError("zero polynomial has no primitive normalization")
    primitive = tuple(Fraction(coefficient // content) for coefficient in integers)
    scale = Fraction(content, denominator)
    if scale <= 0 or polynomial_scale(primitive, scale) != polynomial:
        raise ValueError("invalid positive primitive normalization")
    return scale, primitive


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def format_polynomial(polynomial: Polynomial) -> str:
    terms: list[tuple[str, str]] = []
    for degree in range(len(polynomial) - 1, -1, -1):
        coefficient = polynomial[degree]
        if coefficient == 0:
            continue
        sign = "-" if coefficient < 0 else "+"
        absolute = abs(coefficient)
        if degree == 0:
            body = format_fraction(absolute)
        else:
            variable = "x" if degree == 1 else f"x^{degree}"
            body = variable if absolute == 1 else f"{format_fraction(absolute)}*{variable}"
        terms.append((sign, body))
    if not terms:
        return "0"
    first_sign, first_body = terms[0]
    rendered = ("-" if first_sign == "-" else "") + first_body
    for sign, body in terms[1:]:
        rendered += f" {sign} {body}"
    return rendered


def sign_at_infinity(polynomial: Polynomial, negative: bool) -> int:
    degree = len(polynomial_trim(polynomial)) - 1
    leading = polynomial[degree]
    sign = 1 if leading > 0 else -1
    if negative and degree % 2 == 1:
        sign = -sign
    return sign


def variation_count(signs: tuple[int, ...]) -> int:
    return sum(left != right for left, right in zip(signs, signs[1:]))


def sturm_certificate_payload() -> bytes:
    # A_8 is entered directly from the exact Appell table, low degree first.
    a8: Polynomial = (
        Fraction(1904369, 32531625),
        Fraction(0),
        Fraction(-9388, 8505),
        Fraction(0),
        Fraction(434, 135),
        Fraction(0),
        Fraction(-28, 9),
        Fraction(0),
        Fraction(1),
    )
    sequence = [a8, polynomial_derivative(a8)]
    quotients: list[Polynomial] = []
    while True:
        quotient, remainder = polynomial_divmod(sequence[-2], sequence[-1])
        quotients.append(quotient)
        if remainder == (Fraction(0),):
            break
        sequence.append(polynomial_negate(remainder))

    degrees = tuple(len(polynomial_trim(polynomial)) - 1 for polynomial in sequence)
    if degrees != tuple(range(8, -1, -1)) or len(quotients) != 8:
        raise ValueError(f"unexpected A_8 Sturm degrees or quotient count: {degrees}")
    negative_signs = tuple(sign_at_infinity(polynomial, True) for polynomial in sequence)
    positive_signs = tuple(sign_at_infinity(polynomial, False) for polynomial in sequence)
    expected_negative = (1, -1, 1, -1, 1, 1, 1, -1, 1)
    expected_positive = (1, 1, 1, 1, 1, -1, 1, 1, 1)
    if negative_signs != expected_negative or positive_signs != expected_positive:
        raise ValueError("unexpected limiting sign vectors in A_8 Sturm chain")
    negative_variations = variation_count(negative_signs)
    positive_variations = variation_count(positive_signs)
    if (negative_variations, positive_variations) != (6, 2):
        raise ValueError("unexpected A_8 Sturm variation counts")
    if sequence[-1][0] <= 0:
        raise ValueError("A_8 Sturm chain did not end in a positive constant")

    lines = [
        "Exact Sturm-chain certificate for the inverse-moment Appell polynomial A_8",
        "============================================================================",
        "",
        "Generated exactly by audit/build_asset_manifest.py using fractions.Fraction.",
        "No floating-point arithmetic enters this certificate.",
        "",
        "Definition",
        "----------",
        f"A_8(x) = {format_polynomial(a8)}",
        "S_0 = A_8, S_1 = A_8', and S_{j+1} = -rem(S_{j-1}, S_j) in Q[x].",
        "",
        "Rational Sturm terms and primitive integer normalizations",
        "---------------------------------------------------------",
        "For every j, S_j = c_j P_j, c_j > 0, and P_j is primitive over Z.",
        "The positive scale preserves every limiting sign.",
        "",
    ]
    for index, polynomial in enumerate(sequence):
        scale, primitive = primitive_integer_form(polynomial)
        lines.extend(
            [
                f"j = {index}; degree = {len(polynomial) - 1}",
                f"S_{index}(x) = {format_polynomial(polynomial)}",
                f"c_{index} = {format_fraction(scale)}",
                f"P_{index}(x) = {format_polynomial(primitive)}",
                f"check: S_{index} = c_{index} P_{index}",
                "",
            ]
        )

    lines.extend(
        [
            "Exact Euclidean recurrence",
            "--------------------------",
            "For divisions 1 through 7, S_{j-1} = Q_j S_j - S_{j+1}.",
            "Division 8 has zero remainder: S_7 = Q_8 S_8.",
            "",
        ]
    )
    for division, quotient in enumerate(quotients, start=1):
        lines.append(f"Q_{division}(x) = {format_polynomial(quotient)}")
        if division < 8:
            lines.append(
                f"S_{division - 1} = Q_{division} S_{division} - S_{division + 1}"
            )
        else:
            lines.append("S_7 = Q_8 S_8  (remainder 0)")
        lines.append("")

    render_signs = lambda signs: "(" + ", ".join("+" if sign > 0 else "-" for sign in signs) + ")"
    lines.extend(
        [
            "Limiting signs and Sturm variations",
            "-----------------------------------",
            f"sign(S_0,...,S_8) at -infinity = {render_signs(negative_signs)}",
            f"V(-infinity) = {negative_variations}",
            f"sign(S_0,...,S_8) at +infinity = {render_signs(positive_signs)}",
            f"V(+infinity) = {positive_variations}",
            "",
            "Therefore A_8 has V(-infinity)-V(+infinity) = 6-2 = 4 distinct real roots.",
            "The final positive nonzero constant S_8 proves gcd(A_8,A_8')=1, so A_8 is square-free.",
            "Its other four roots are nonreal and form two conjugate pairs.",
            "",
        ]
    )
    return "\n".join(lines).encode("ascii")


def expected_asset_files() -> set[str]:
    copied = {
        entry.canonical_destination.removeprefix("assets/")
        for entry in ENTRIES.values()
        if entry.copy_payload
    }
    return copied | {
        "README.md",
        "endpoint/dyadic-completion/figures/dyadic_tail_convergence.png",
        "endpoint/dyadic-completion/figures/psi_periodic.png",
        "requirements.txt",
        "self-sampling/appell_a8_sturm_certificate.txt",
    }


def actual_asset_files() -> set[str]:
    return {
        path.relative_to(ASSET_ROOT).as_posix()
        for path in ASSET_ROOT.rglob("*")
        if path.is_file()
    }


def write_or_check(path: Path, payload: bytes, check: bool) -> None:
    if check:
        if not path.is_file():
            raise FileNotFoundError(f"missing generated file: {path}")
        actual = path.read_bytes()
        if actual != payload:
            raise ValueError(f"generated file is stale: {path}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)


def validate_no_duplicate_assets() -> None:
    groups: defaultdict[str, list[str]] = defaultdict(list)
    for path in ASSET_ROOT.rglob("*"):
        if path.is_file():
            groups[sha256_file(path)].append(path.relative_to(ASSET_ROOT).as_posix())
    duplicates = {digest: names for digest, names in groups.items() if len(names) > 1}
    if duplicates:
        detail = "; ".join(
            f"{digest}: {', '.join(names)}" for digest, names in sorted(duplicates.items())
        )
        raise ValueError(f"duplicate canonical asset payloads: {detail}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify the existing migration and disposition data without writing",
    )
    args = parser.parse_args()
    try:
        files = source_files()
        if len(files) != 88:
            raise ValueError(f"expected 88 audited source files, found {len(files)}")
        missing = sorted(set(files) - set(ENTRIES))
        obsolete = sorted(set(ENTRIES) - set(files))
        if missing or obsolete:
            raise ValueError(
                "disposition coverage mismatch; "
                f"missing={missing!r}; obsolete={obsolete!r}"
            )

        for source, entry in ENTRIES.items():
            if not entry.copy_payload:
                continue
            destination = CANONICAL_ROOT / entry.canonical_destination
            payload = transformed_payload(files[source], entry)
            write_or_check(destination, payload, args.check)

        write_or_check(STURM_CERTIFICATE, sturm_certificate_payload(), args.check)

        expected = expected_asset_files()
        actual = actual_asset_files()
        if actual != expected:
            raise ValueError(
                "canonical asset file set differs; "
                f"missing={sorted(expected - actual)!r}; "
                f"unexpected={sorted(actual - expected)!r}"
            )

        # Verify source duplicates deliberately mapped to one retained payload.
        for source, entry in ENTRIES.items():
            if entry.disposition != "deduplicated_to_retained_payload":
                continue
            destination = CANONICAL_ROOT / entry.canonical_destination
            if sha256_bytes(files[source]) != sha256_file(destination):
                raise ValueError(f"deduplication target differs from source: {source}")

        rows = disposition_rows(files)
        write_or_check(DISPOSITION_CSV, csv_payload(rows), args.check)
        validate_no_duplicate_assets()

        dispositions = Counter(row["disposition"] for row in rows)
        asset_count = len(actual_asset_files())
        mode = "verified" if args.check else "built"
        print(f"asset migration {mode}")
        print(f"source disposition rows: {len(rows)}")
        print(f"canonical payloads: {asset_count}")
        print("dispositions:")
        for disposition, count in sorted(dispositions.items()):
            print(f"  {disposition:46s} {count:3d}")
        print("duplicate canonical payloads: 0")
        return 0
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
