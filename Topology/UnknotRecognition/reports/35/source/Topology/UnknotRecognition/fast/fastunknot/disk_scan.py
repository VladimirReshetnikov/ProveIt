"""Opt-in full radical transfer after adaptive sparse and residue shortcuts.

The partially cancelled complex is immutable during a transfer attempt. Only
a completed, disk-certified reduction is installed. The default local poll
allowance is an experimental overhead guard, not a bit-operation bound.
"""
from .disk_frontier import GeometryError, certify_disk
from .radical_transfer import snapshot, reduce_complex
from .residue import AdaptiveScan


class TransferLimit(Exception):
    """Local experimental transfer allowance; resume ordinary cancellation."""


class DiskAdaptiveScan(AdaptiveScan):
    def __init__(self, *args, transfer_polls=None, **kwargs):
        if transfer_polls is not None and (type(transfer_polls) is not int or transfer_polls < 0):
            raise ValueError("transfer_polls must be nonnegative or None")
        super().__init__(*args, **kwargs)
        self.transfer_polls = transfer_polls
        self.processed_crossings = []
        self.stats.update(disk_attempts=0, disk_transfers=0, disk_declines=0,
                          disk_budget_fallbacks=0, disk_polls=0,
                          disk_transfer_compositions=0, disk_max_delta_factors=0)

    def add_crossing(self, slots, reduce_now=True):
        # Cancellation happens inside super().add_crossing. Its committed
        # frontier therefore already includes this crossing when queried.
        self.processed_crossings.append(tuple(slots))
        super().add_crossing(slots, reduce_now=reduce_now)

    def _try_profile(self):
        if super()._try_profile():
            return True
        return self._try_transfer()

    def _try_transfer(self):
        stats = self.stats
        stats["disk_attempts"] += 1
        allowance = self.transfer_polls
        if allowance is None:
            allowance = max(4096, 64 * self.live)
        used = 0

        def poll():
            nonlocal used
            self._check()  # A global failure must not be downgraded to local decline.
            if used >= allowance:
                raise TransferLimit("local full-transfer allowance exhausted")
            used += 1

        try:
            poll()
            cert = certify_disk(self.processed_crossings, check=poll)
            if set(cert.cyclic_order) != set(self.points):
                raise GeometryError("processed prefix and current frontier disagree")
            poll()
            before = self.live
            original = snapshot(self)
            red = reduce_complex(original, self.algebra, poll=poll,
                                 cyclic_order=cert.cyclic_order)
            c = red.complex
            inc = [set() for _ in c.mid]
            for j, row in enumerate(c.out):
                poll()
                for k in row:
                    inc[k].add(j)
            poll()
        except GeometryError:
            stats["disk_declines"] += 1
            return False
        except TransferLimit:
            stats["disk_budget_fallbacks"] += 1
            return False
        finally:
            stats["disk_polls"] += used
        # No partial differential or partially constructed incidence data are
        # ever visible to the scanner. Its algebra's typed caches remain valid.
        self.mid, self.deg, self.out, self.inc, self.live = c.mid, c.deg, c.out, inc, c.n
        self.composed.clear()
        stats["eliminations"] += (before - c.n) // 2
        stats["compositions"] += red.stats["compositions"]
        stats["disk_transfer_compositions"] += red.stats["compositions"]
        stats["disk_max_delta_factors"] = max(stats["disk_max_delta_factors"], red.stats["max_delta_factors"])
        stats["disk_transfers"] += 1
        return True
