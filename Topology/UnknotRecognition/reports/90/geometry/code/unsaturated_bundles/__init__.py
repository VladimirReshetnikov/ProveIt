"""Proper-boundary interval-bundle reduction, conditional on actual geometry."""

from .finite import census, make_certificate
from .replay import verify_certificate

__all__ = ['census', 'make_certificate', 'verify_certificate']
