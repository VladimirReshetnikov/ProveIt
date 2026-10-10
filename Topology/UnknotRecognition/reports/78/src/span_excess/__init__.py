"""Research kernels for defect-stratified cocycle surface optimization."""
from .model import HeightModel, WorkLimit
from .strata import Stratum, stratum_count, containing_stratum, constraints_for
from .search import optimize_band
from .checker import replay_band, replay_cell
__all__ = ['HeightModel', 'WorkLimit', 'Stratum', 'stratum_count',
           'containing_stratum', 'constraints_for', 'optimize_band',
           'replay_band', 'replay_cell']
from .lexicographic import minimize_edge_then_span, replay_edge_then_span
__all__ += ['minimize_edge_then_span', 'replay_edge_then_span']
