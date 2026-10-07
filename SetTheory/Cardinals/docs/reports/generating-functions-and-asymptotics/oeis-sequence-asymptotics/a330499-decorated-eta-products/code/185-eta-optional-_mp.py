"""High-precision A330499 functions; h[j] denotes H_j(sqrt(x))."""
import mpmath as mp
from _common import odd_sigma, require


def constants():
    mu = mp.e - 1
    return mu, 1 - mp.exp(-1), mp.pi**2 / (12 * mu)


def harmonics(x, modes=30):
    """Truncated H0/H1/H2 from the Report185 A330499 formula, no fitted constants."""
    require(x > 0 and 1 <= modes <= 100, "invalid harmonic parameters")
    mu, _, _ = constants()
    h = [mp.mpf(0) for _ in range(3)]
    u = (2 * mu**2 - 1) / 12
    for m in range(1, modes + 1):
        a = 2 * mp.pi**2 * m / mu
        weight = mp.mpf(odd_sigma(m)) / m * mp.exp(-a / 2) * a**mp.mpf(".25") / mp.sqrt(mp.pi)
        phase = 2 * mp.sqrt(a * x) + mp.pi / 4
        first = u * a**mp.mpf("1.5") + 3 / (16 * mp.sqrt(a))
        second = (-a**3 * u**2 / 2 + a**2 * (mu**3 / 24 + mu**2 / 12)
                  - 15 * a * u / 16 + 15 / (512 * a))
        h[0] -= weight * mp.cos(phase)
        h[1] += weight * first * mp.sin(phase)
        h[2] -= weight * second * mp.cos(phase)
    return h


def scaled_exact(value, n):
    _, rho, constant = constants()
    return (mp.mpf(value) * rho**n / mp.factorial(n) - constant) * mp.mpf(n)**mp.mpf(".75")


def decimal(x, digits=40):
    require(mp.isfinite(x), "non-finite numerical result")
    return mp.nstr(x, digits)


def inverse_row(value, n, modes=30):
    """Roots of two named smooth models at Y=a(n), not a discrete inverse oracle."""
    _, rho, constant = constants()
    target = mp.log(value)
    core_model = lambda x: mp.loggamma(x + 1) - x * mp.log(rho) + mp.log(constant)
    core = mp.findroot(lambda x: core_model(x) - target, (n - 1, n + 1))
    derivative = mp.digamma(core + 1) - mp.log(rho)
    require(core > 0 and derivative > 0, "invalid factorial-core root")
    shifted = core - core**mp.mpf("-.75") * harmonics(core, modes)[0] / (constant * derivative)

    def three_term_model(x):
        hs = harmonics(x, modes)
        amplitude = constant + sum(x**(-mp.mpf(".75") - mp.mpf(j) / 2) * hs[j]
                                   for j in range(3))
        require(x > 0 and amplitude > 0, "smooth-model log outside positive range")
        return mp.loggamma(x + 1) - x * mp.log(rho) + mp.log(amplitude)

    root = mp.findroot(lambda x: three_term_model(x) - target, (n - 1, n + 1))
    return {
        "core_inverse_error": core - n,
        "first_inverse_error": shifted - n,
        "three_term_inverse_error": root - n,
        "core_log_equation_residual": core_model(core) - target,
        "three_term_log_equation_residual": three_term_model(root) - target,
    }
