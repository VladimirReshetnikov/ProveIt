"""Validated lazy selection of optional one-sided Jones filters."""
from .filters import jones_obstruction

JONES_BACKENDS = ("matching", "potts5", "potts-exact", "potts-exact-factorized", "potts-separator")


def validate_jones_options(backend, colors, max_states, max_transitions):
    if backend not in JONES_BACKENDS:
        raise ValueError("unknown Jones backend")
    if type(colors) is not int or colors < 5:
        raise ValueError("potts_colors must be an integer at least 5")
    for name, value in (("max_states", max_states), ("max_transitions", max_transitions)):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name + " must be a nonnegative integer or None")


def select_jones_filter(backend, colors=6):
    """Return evaluator, evidence method, and its specialization options."""
    validate_jones_options(backend, colors, None, None)
    if backend == "matching":
        return jones_obstruction, "jones-modular", {}
    if backend == "potts5":
        from .potts import potts_obstruction
        return potts_obstruction, "jones-potts5-modular", {}
    if backend == "potts-exact":
        from .potts_exact import potts_exact_obstruction
        return potts_exact_obstruction, "jones-potts-exact", {"colors": colors}
    if backend == "potts-separator":
        from .separator_potts import separator_potts_obstruction
        return separator_potts_obstruction, "jones-potts-separator", {"colors": colors}
    from .potts_factorized_exact import factorized_potts_exact_obstruction
    return factorized_potts_exact_obstruction, "jones-potts-exact-factorized", {"colors": colors}
