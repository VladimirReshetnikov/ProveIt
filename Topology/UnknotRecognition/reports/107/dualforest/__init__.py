"""Research kernels for dual-forest cancellation selection; no topology oracle."""
from .model import Instance, make_instance, from_dense, from_data
from .solver import solve, solve_pair
from .verify import verify_positive, verify_pair_optimality, verify_negative
__all__ = ["Instance", "make_instance", "from_dense", "from_data", "solve",
           "solve_pair", "verify_positive", "verify_pair_optimality", "verify_negative"]
