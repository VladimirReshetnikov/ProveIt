"""Certified rank-two braid kernels. Not a general quasipolynomial recognizer."""
from .kernel import compress, optimal_pass, maximal_corridors, Replacement
from .verify import verify

__all__ = ['compress', 'optimal_pass', 'maximal_corridors', 'Replacement', 'verify']
__version__ = '0.1.0'
