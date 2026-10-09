"""Cached positive-zeta oracle using the unchanged, certified AHT count kernel."""
from .geometry import natural, prepare, selected_union, cone_rows
from .kernels import load_kernel
from .reconstruct import ResourceExhausted

class OrbitZetaOracle:
    def __init__(self, size, pairings, ports, *, max_cycles=None, max_queries=None,
                 check=None, record_certificate=False):
        self.check = check if check is not None else lambda: None
        self.check()
        for value, label in ((max_cycles, 'max_cycles'), (max_queries, 'max_queries')):
            if value is not None:
                natural(value, label)
        if type(record_certificate) is not bool:
            raise ValueError('record_certificate must be bool')
        self.size, self.rows, self.ports = prepare(size, pairings, ports, self.check)
        self.rank = len(self.ports)
        self.full = (1 << self.rank)-1
        self.max_cycles, self.max_queries = max_cycles, max_queries
        self.record = record_certificate
        self.stats = dict(orbit_calls=0, cycles=0, zeta_requests=0, zeta_cache_hits=0,
                          union_cache_hits=0, union_constructions=0)
        self.kernel = load_kernel('interval_orbits')
        self.base = None
        self.zeta_cache = {}
        self.unions = {}

    def _count(self, rows):
        self.check()
        if self.max_queries is not None and self.stats['orbit_calls'] >= self.max_queries:
            raise ResourceExhausted('orbit query allowance exhausted')
        remaining = (None if self.max_cycles is None else
                     self.max_cycles-self.stats['cycles'])
        pairs = [self.kernel.IntervalPairing(a,b,c,d,sign == -1)
                 for a,b,c,d,sign in rows]
        self.stats['orbit_calls'] += 1
        answer = self.kernel.count_orbits(self.size, pairs, max_cycles=remaining,
            periodic_rule='aht', check=self.check, record_certificate=self.record)
        self.stats['cycles'] += answer.cycles
        if not answer.complete:
            raise ResourceExhausted('total AHT cycle allowance exhausted')
        return answer

    def initialize(self):
        if self.base is None:
            self.base = self._count(self.rows)
            self.zeta_cache[self.full] = self.base.orbits
        return self.base.orbits

    def __call__(self, mask):
        self.check()
        natural(mask, 'zeta mask')
        if mask > self.full:
            raise ValueError('zeta mask outside port set')
        self.initialize()
        self.stats['zeta_requests'] += 1
        if mask in self.zeta_cache:
            self.stats['zeta_cache_hits'] += 1
            return self.zeta_cache[mask]
        union = selected_union(self.ports, self.full ^ mask, self.check)
        self.stats['union_constructions'] += 1
        if not union:
            value = self.base.orbits
        else:
            if union in self.unions:
                self.stats['union_cache_hits'] += 1
            else:
                self.unions[union] = self._count(self.rows + cone_rows(union))
            # C - H(A) = C_A - 1 for nonempty A.
            value = self.unions[union].orbits - 1
        if not 0 <= value <= self.base.orbits:
            raise AssertionError('coned orbit count violates incidence identity')
        self.zeta_cache[mask] = value
        return value

    def certificate(self, entries):
        """Select only the proofs needed by the independent sparse verifier.

        All extra queries use the same remaining allowances as discovery.
        No dense subset table and no proof of a discovery-only query is emitted.
        """
        if not self.record:
            raise ValueError('certificate recording was not enabled')
        self.initialize()
        masks = {0}
        for mask, _ in entries:
            if mask:
                masks.add(mask)
                bits = mask
                while bits:
                    bit = bits & -bits
                    masks.add(mask ^ bit)
                    bits ^= bit
        needed = {}
        for mask in sorted(masks):
            self.check()
            self(mask)
            union = selected_union(self.ports, self.full ^ mask, self.check)
            if union:
                needed[union] = self.unions[union].certificate
        return dict(schema='sparse-incidence-v1', size=self.size,
                    pairings=[list(row) for row in self.rows],
                    ports=[[list(x) for x in port] for port in self.ports],
                    total=self.base.orbits, entries=[list(row) for row in entries],
                    baseline=self.base.certificate,
                    union_proofs=[dict(union=[list(x) for x in union], proof=proof)
                                  for union, proof in sorted(needed.items())])
