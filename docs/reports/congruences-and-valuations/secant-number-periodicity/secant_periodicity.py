"""Exact modular periodicity of the positive secant numbers (OEIS A000364).

Python 3.9+; standard library only. All mathematical computations are exact.
Factorization uses trial division: pass modest moduli, or use the prime-power
functions after obtaining a factorization elsewhere. See article.pdf for proofs.
"""

from dataclasses import dataclass
from functools import lru_cache
from math import comb, lcm
from typing import Dict, Optional, Sequence, Tuple


def _integer_at_least(value: int, minimum: int, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
        raise ValueError("{} must be an integer >= {}".format(name, minimum))


def factor_integer(value: int) -> Dict[int, int]:
    """Return the prime factorization of a positive integer by trial division."""
    _integer_at_least(value, 1, "value")
    factors: Dict[int, int] = {}
    candidate = 2
    while candidate * candidate <= value:
        while value % candidate == 0:
            factors[candidate] = factors.get(candidate, 0) + 1
            value //= candidate
        candidate += 1 if candidate == 2 else 2
    if value > 1:
        factors[value] = 1
    return factors


def is_prime(value: int) -> bool:
    if not isinstance(value, int) or isinstance(value, bool) or value < 2:
        return False
    return factor_integer(value) == {value: 1}


def valuation(value: int, prime: int) -> int:
    """Exponent of prime in a nonzero integer (prime is assumed prime)."""
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError("value must be a nonzero integer")
    if value == 0:
        raise ValueError("valuation(0) is infinite and is not represented here")
    _integer_at_least(prime, 2, "prime")
    value = abs(value)
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


@lru_cache(maxsize=32)
def secant_numbers(maximum_index: int) -> Tuple[int, ...]:
    """a[0..maximum_index], using sec(x)*cos(x)=1 and integer arithmetic."""
    _integer_at_least(maximum_index, 0, "maximum_index")
    values = [1]
    for n in range(1, maximum_index + 1):
        values.append(sum(
            (1 if j % 2 else -1) * comb(2 * n, 2 * j) * values[n - j]
            for j in range(1, n + 1)
        ))
    return tuple(values)


def secant_numbers_entringer(maximum_index: int) -> Tuple[int, ...]:
    """Independent construction: even-row endpoints of Entringer's triangle.

    E(n,0)=0, E(n,k)=E(n,k-1)+E(n-1,n-k), E(0,0)=1.
    This is substantially faster than repeated binomial evaluation at large n.
    """
    _integer_at_least(maximum_index, 0, "maximum_index")
    row = [1]
    result = [1]
    for n in range(1, 2 * maximum_index + 1):
        new_row = [0]
        running_sum = 0
        for value in reversed(row):
            running_sum += value
            new_row.append(running_sum)
        row = new_row
        if n % 2 == 0:
            result.append(running_sum)
    return tuple(result)


def _prime_power_arguments(prime: int, exponent: int) -> None:
    _integer_at_least(exponent, 1, "exponent")
    if not is_prime(prime):
        raise ValueError("prime must be a prime number")


def prime_power_period(prime: int, exponent: int) -> int:
    """The LEAST eventual period of a(n) modulo prime**exponent."""
    _prime_power_arguments(prime, exponent)
    if prime == 2:
        return 1 if exponent <= 2 else 2 ** (exponent - 1)
    return prime ** (exponent - 1) * lcm(2, (prime - 1) // 2)


def prime_power_preperiod(
    prime: int, exponent: int, values: Optional[Sequence[int]] = None
) -> int:
    """Least index s>=0 for which a(n) modulo p**e is periodic for all n>=s.

    Only a[0..ceil(e/2)-1] are inspected. An optional values argument must
    contain the actual integer secant numbers, not their residues.
    """
    _prime_power_arguments(prime, exponent)
    if prime == 2:
        return 0
    height = (exponent + 1) // 2
    if values is None:
        values = secant_numbers(height - 1)
    if len(values) < height:
        raise ValueError("values must include indices 0 through ceil(e/2)-1")
    for n in range(height - 1, -1, -1):
        if values[n] == 0:
            raise ValueError("secant numbers are nonzero")
        if 2 * n + valuation(values[n], prime) < exponent:
            return n + 1
    raise AssertionError("a(0)=1 guarantees a nonempty transient at odd primes")


@dataclass(frozen=True)
class PeriodData:
    modulus: int
    factorization: Tuple[Tuple[int, int], ...]
    preperiod: int
    period: int

    @property
    def pure_from_index_one(self) -> bool:
        return self.preperiod <= 1


def analyze_modulus(modulus: int) -> PeriodData:
    """Exact least eventual period and onset, including modulus 1."""
    _integer_at_least(modulus, 1, "modulus")
    factors = factor_integer(modulus)
    onset, period = 0, 1
    for prime, exponent in factors.items():
        onset = max(onset, prime_power_preperiod(prime, exponent))
        period = lcm(period, prime_power_period(prime, exponent))
    return PeriodData(modulus, tuple(factors.items()), onset, period)


def euler_phi(modulus: int) -> int:
    _integer_at_least(modulus, 1, "modulus")
    result = modulus
    for prime in factor_integer(modulus):
        result = result // prime * (prime - 1)
    return result


def secant_mod_odd(index: int, modulus: int) -> int:
    """Compute a(index) modulo an ODD modulus by a finite moment formula.

    Cost: modulus modular exponentiations; O(1) extra storage. This is suitable
    for a huge index and a modest modulus, NOT for a huge modulus.
    Python's pow(0, 0, modulus)=1 convention is exactly the one needed at n=0.
    """
    _integer_at_least(index, 0, "index")
    _integer_at_least(modulus, 1, "modulus")
    if modulus % 2 == 0:
        raise ValueError("modulus must be odd")
    total = 0
    for j in range(modulus):
        odd = 2 * j + 1
        term = pow(-(odd * odd), index, modulus)
        total += term if j % 2 == 0 else -term
    return total % modulus


def density_cutoff(index: int, prime: int, values: Sequence[int]) -> int:
    """c_p(N)=min_{n>=N}(2n+v_p(a_n)), for N>=1 and an odd prime.

    The infinite minimum needs only indices N..N+floor(v_p(a_N)/2).
    """
    _integer_at_least(index, 1, "index")
    if prime == 2 or not is_prime(prime):
        raise ValueError("prime must be an odd prime")
    if len(values) <= index:
        raise ValueError("values must include a(index)")
    last = index + valuation(values[index], prime) // 2
    if len(values) <= last:
        raise ValueError("additional secant numbers are required")
    return min(2 * n + valuation(values[n], prime)
               for n in range(index, last + 1))
