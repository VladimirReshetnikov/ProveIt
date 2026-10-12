"""Exact positive-singleton cancellation research kernels. No topology oracle."""
from .peeling import column_cancellation_plan
from .verify import verify_peeling_certificate, verify_stopping_set, replay_positive
from .deferred import deferred_plan, replay_with_passive, transport_exact_counts
__all__ = ['column_cancellation_plan', 'verify_peeling_certificate',
           'verify_stopping_set', 'replay_positive', 'deferred_plan', 'replay_with_passive', 'transport_exact_counts']
