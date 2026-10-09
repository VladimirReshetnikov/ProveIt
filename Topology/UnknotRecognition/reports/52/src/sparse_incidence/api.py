"""Public query interface. COMPLETE refers to incidence, never to unknot recognition."""
from .oracle import OrbitZetaOracle
from .reconstruct import discover, ResourceExhausted

def analyze(size, pairings, ports, *, strategy='balanced', max_cycles=None,
            max_queries=None, max_entries=None, check=None, record_certificate=False):
    oracle = OrbitZetaOracle(size, pairings, ports, max_cycles=max_cycles,
        max_queries=max_queries, check=check, record_certificate=record_certificate)
    try:
        result = discover(oracle.rank, oracle, strategy=strategy,
                          max_entries=max_entries, check=oracle.check)
        certificate = oracle.certificate(result['entries']) if record_certificate else None
        return dict(status='COMPLETE', total=result['total'],
                    histogram=[list(row) for row in result['entries']],
                    certificate=certificate,
                    stats={**oracle.stats, **result['stats']})
    except ResourceExhausted as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), total=None,
                    histogram=None, certificate=None, stats=dict(oracle.stats))

def dense_ablation(size, pairings, ports, *, max_ports=16):
    """Cached dense Möbius baseline with the identical AHT kernel.

    A research ablation, not a byte-for-byte copy of upstream dispatch.
    max_ports is an allocation guard, not a claim about geometric width.
    """
    oracle = OrbitZetaOracle(size, pairings, ports)
    if oracle.rank > max_ports:
        raise ValueError('dense ablation port cap exceeded')
    values = [oracle(mask) for mask in range(1 << oracle.rank)]
    for bit in range(oracle.rank):
        step = 1 << bit
        for mask in range(len(values)):
            if mask & step:
                values[mask] -= values[mask ^ step]
    if any(v < 0 for v in values):
        raise AssertionError('negative histogram')
    return dict(histogram=[[m,v] for m,v in enumerate(values) if v],
                dense=values, stats=oracle.stats)
