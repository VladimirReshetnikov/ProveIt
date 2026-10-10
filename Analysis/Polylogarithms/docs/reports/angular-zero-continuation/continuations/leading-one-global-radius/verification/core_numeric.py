"""Exploratory quadrature for leading-index-one double polylogarithms.

These floating-point routines are not interval certificates. The separate
verify_exact.py script certifies selected root brackets using rational series.
"""
from __future__ import annotations
import numpy as np
from scipy.special import roots_genlaguerre, gamma
from scipy.optimize import brentq

class LeadingOne:
    def __init__(self, b: float, order: int = 128):
        if not np.isfinite(b) or b <= 0:
            raise ValueError('b must be positive and finite')
        if not 16 <= order <= 300:
            raise ValueError('quadrature order must lie between 16 and 300')
        nodes, weights = roots_genlaguerre(order, b - 1)
        self.b = float(b)
        self.t = np.exp(-nodes)
        self.weights = weights / gamma(b)
        if not np.isfinite(self.weights).all():
            raise ArithmeticError('nonfinite quadrature weights')

    def value(self, z: complex) -> complex:
        z = complex(z)
        if z.imag == 0 and z.real >= 1:
            raise ValueError('principal cut [1,infinity) is excluded')
        t = self.t
        log_1z = np.log1p(-z)
        ratio = np.empty(t.shape, dtype=complex)
        small = t < 1e-7
        # Avoid loss of significance and 0/0 at underflowed t.
        ratio[small] = -z - t[small] * z*z / 2 - t[small]**2 * z**3 / 3
        ratio[~small] = np.log1p(-t[~small]*z) / t[~small]
        kernel = (ratio - log_1z)/(1-t)
        return complex(np.dot(self.weights, kernel))

    def eta(self, rho: float) -> float:
        if not 0 <= rho <= 1:
            raise ValueError('rho must lie in [0,1]')
        if rho == 0:
            return (1+2**(-self.b))/3
        def equation(eta: float) -> float:
            x = rho*rho*eta
            y = rho*np.sqrt(max(0.,1-rho*rho*eta*eta))
            return self.value(complex(x,y)).imag / y
        return float(brentq(equation, 1e-7, 1-1e-7, xtol=4e-15))
