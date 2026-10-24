"""Smaller positive-power certificates; all variables are natural numbers.

The certificate is a restricted complete subfamily of the Pell criterion.
See the report for the two-direction argument; this code is not a formal proof.
"""
from base_builder import Builder as OriginalBuilder, ONE, TWO, FOUR


class PowerBuilder(OriginalBuilder):
    def norm(self, a, x, y, label, guard=None):
        if guard is not None:
            return super().norm(a, x, y, label, guard)
        ay = self.mul(a, y)
        self.row([(1, [x, x]), (1, [y, y]), (-1, [ay, ay]), (-1, [])], label)

    def power(self, n, k):
        if not self.positive_powers:
            return super().power(n, k)
        key = (n, k)
        if key in self.powers:
            return self.powers[key]
        tag = f"pow{len(self.powers)}"
        start = len(self.variables)
        m = self.new(tag + ".output")
        self.powers[key] = m
        W = self.add(n, k)
        A = self.new(tag + ".A")
        yk = self.new(tag + ".slack.yk")
        Y = self.add(k, yk)
        gap = self.new(tag + ".slack.gap")
        T = self.sum([m, gap, ONE])
        Z, X = [self.new(tag + "." + s) for s in ("Z", "X")]
        U, V, S, R, B = [self.new(tag + ".pell." + s) for s in ("U", "V", "S", "R", "B")]
        self.norm(A, X, Y, tag + ".norm1")
        self.norm(A, U, V, tag + ".norm2")
        self.norm(B, S, R, tag + ".norm3")
        q4minus1 = self.new(tag + ".q4minus1")
        fourY = self.mul(FOUR, Y)
        self.eq(B, self.add(ONE, self.mul(fourY, self.add(q4minus1, ONE))), tag + ".B_mod_4Y")
        vd = self.new(tag + ".Vquotient_minus1")
        self.eq(V, self.mul(self.square(Y), self.add(vd, ONE)), tag + ".V_positive_multiple")
        for left, right, modulus, label in [
            (B, A, U, "B_mod_U"),
            (S, X, U, "S_mod_U"),
            (R, k, fourY, "R_mod_4Y"),
            (self.add(X, self.mul(Y, n)), self.add(self.mul(Y, A), m), T, "power_congruence"),
        ]:
            q = self.new(tag + "." + label + ".quotient")
            self.eq(left, self.add(right, self.mul(modulus, q)), tag + "." + label)
        self.eq(self.product([TWO, A, n]), self.sum([T, self.square(n), ONE]), tag + ".T_definition")
        self.norm(self.add(W, ONE), A, self.mul(W, Z), tag + ".last_norm")
        self.macro_log.append({"macro": "power", "output": m, "base": n, "exponent": k,
                               "first_variable": start, "end_variable": len(self.variables)})
        return m
