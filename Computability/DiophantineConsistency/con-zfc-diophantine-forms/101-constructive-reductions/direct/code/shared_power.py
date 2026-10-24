"""Simultaneous positive-power certificates over the nonnegative integers.

Import this module with the pinned upstream ``direct`` directory on sys.path.
The upstream Builder supplies only natural addition/multiplication gates and
the exact quartic exporter. This subclass shares a Pell scale across all
positive exponentiation calls, index certificates by exponent, and the
power modulus by base. Internal quotients have proved nonnegative signs;
remaining outer congruences use one common signed-quotient offset.

The semantic circuit must call power only with positive base and exponent;
the proof and audit describe this inherited obligation explicitly.
"""
from __future__ import annotations

from build_equation import Builder, ZERO, ONE, TWO, FOUR, require


class SharedPowerBuilder(Builder):
    def __init__(self, positive_powers=True, **kwargs):
        require(positive_powers, "shared positive-power builder needs positive inputs")
        require(not kwargs, "unsupported builder options")
        super().__init__(positive_powers=True)
        self.shared_parameters = None
        self.shared_offset = None
        self.shared_indices = {}
        self.shared_bases = {}
        self.shared_frame_finalized = False

    def congruent(self, left, right, modulus, label, guard=None):
        require(guard is None, "shared quotient offset supports unguarded congruences")
        if self.shared_offset is None:
            self.shared_offset = self.new("shared.congruence_offset")
        quotient = self.fresh(label + ".q")
        self.eq(self.add(left, self.mul(modulus, quotient)),
                self.add(right, self.mul(modulus, self.shared_offset)), label)

    def _scale(self):
        if self.shared_parameters is None:
            W, A, zm1 = [self.new("shared." + s) for s in ("W", "A", "Zminus1")]
            Z = self.add(zm1, ONE)
            self.norm(self.add(W, ONE), A, self.mul(W, Z), "shared.last_norm")
            self.shared_parameters = W, A, Z
        return self.shared_parameters

    def finalize_power_frame(self):
        """Close the single dominating bound after the semantic DAG is known."""
        if self.shared_frame_finalized:
            return
        require(bool(self.powers), "shared power frame needs at least one call")
        atoms = {a for (n, k), m in self.powers.items() for a in (n, k, m)}
        W, _, _ = self._scale()
        self.eq(W, self.sum([TWO] + sorted(atoms)), "shared.frame_definition")
        self.shared_frame_finalized = True

    def _index(self, k):
        if k in self.shared_indices:
            return self.shared_indices[k]
        _, A, _ = self._scale()
        tag = "index" + str(len(self.shared_indices))
        X, Y, U, V, S, R = [self.new(tag + "." + s)
                            for s in ("X", "Y", "U", "V", "S", "R")]
        yk = self.new(tag + ".YminusK")
        self.eq(Y, self.add(k, yk), tag + ".index_at_most_Y")
        fourY = self.mul(FOUR, Y)
        q4minus1 = self.new(tag + ".q4minus1")
        B = self.add(ONE, self.mul(fourY, self.add(q4minus1, ONE)))
        self.norm(A, X, Y, tag + ".norm1")
        self.norm(A, U, V, tag + ".norm2")
        self.norm(B, S, R, tag + ".norm3")
        vd = self.new(tag + ".Vquotient_minus1")
        self.eq(V, self.mul(self.square(Y), self.add(vd, ONE)), tag + ".V_positive_multiple")
        bq, sq, rq = [self.new(tag + "." + s) for s in ("Bquotient", "Squotient", "Rquotient")]
        self.eq(B, self.add(A, self.mul(U, bq)), tag + ".B_mod_U")
        self.eq(S, self.add(X, self.mul(U, sq)), tag + ".S_mod_U")
        self.eq(R, self.add(k, self.mul(fourY, rq)), tag + ".R_mod_4Y")
        self.shared_indices[k] = X, Y
        return X, Y

    def _base(self, n):
        if n in self.shared_bases:
            return self.shared_bases[n]
        _, A, _ = self._scale()
        tag = "base" + str(len(self.shared_bases))
        T = self.new(tag + ".T")
        self.eq(self.product([TWO, A, n]),
                self.sum([T, self.square(n), ONE]), tag + ".T_definition")
        self.shared_bases[n] = T
        return T

    def power(self, n, k):
        require(not self.shared_frame_finalized, "cannot add a power after frame finalization")
        key = n, k
        if key in self.powers:
            return self.powers[key]
        tag = "pow" + str(len(self.powers))
        start = len(self.variables)
        m = self.new(tag + ".output")
        self.powers[key] = m
        _, A, _ = self._scale()
        X, Y = self._index(k)
        T = self._base(n)
        quotient = self.new(tag + ".quotient")
        self.eq(self.add(X, self.mul(Y, n)),
                self.sum([self.mul(Y, A), m, self.mul(T, quotient)]),
                tag + ".power_congruence")
        self.macro_log.append({"macro": "power", "output": m, "base": n, "exponent": k,
                               "first_variable": start, "end_variable": len(self.variables),
                               "shared_scale": True})
        return m

    def sharing_census(self):
        return {"power_calls": len(self.powers),
                "distinct_exponent_atoms": len(self.shared_indices),
                "distinct_base_atoms": len(self.shared_bases),
                "common_scale_triples": int(self.shared_parameters is not None),
                "common_congruence_offsets": int(self.shared_offset is not None),
                "positive_oriented_internal_quotients": True,
                "global_frame_finalized": self.shared_frame_finalized}

    def export(self, *args, **kwargs):
        self.finalize_power_frame()
        return super().export(*args, **kwargs)
