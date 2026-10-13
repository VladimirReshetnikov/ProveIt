"""Proof-backed private-cocore transport kernels; not a knot recognizer."""
from .core import compile_program, owners, least_private, produce_certificate
from .verify import verify_certificate
from .atlas import build_atlas, query_atlas, find_exceptions
__all__ = ["compile_program", "owners", "least_private", "produce_certificate",
           "verify_certificate", "build_atlas", "query_atlas", "find_exceptions"]
from .core import normalize_matching, produce_matching_certificate
__all__ += ["normalize_matching", "produce_matching_certificate"]
