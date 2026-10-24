"""Direct C222 construction with one shared exponent and a latent Pell index.

The power notation used by this generator is compiled by the included
quadratic Pell graphs. No variable exponent is present in the output equation.
All arithmetic source data and the unchanged compiler are supplied locally.
"""
from pathlib import Path
import sys
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
ENGINE = ROOT / 'upstream' / 'engine'
sys.path[:0] = [str(ENGINE / 'code'), str(ENGINE / 'code/psd_contract'), str(ENGINE)]
import build_projected as parent
from reuse_radix import AdditiveReusedRadixBuilder
from build_equation import ONE, TWO
from contract import contract
import reproduce


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


class SynchronizedExponentBuilder(AdditiveReusedRadixBuilder):
    """One squared factorial radius and one auxiliary unrequested index."""
    def factorial(self, n):
        if n in self.factorials:
            return self.factorials[n]
        tag = 'factorial' + str(len(self.factorials))
        out = self.new(tag + '.output')
        self.factorials[n] = out
        if not hasattr(self, 'shared_rho'):
            self.shared_rho = self.square(out)
        rho = self.shared_rho
        C = self.binomial(self.add(rho, n), n)
        V = self.power(self.add(rho, ONE), n)
        r = self.new(tag + '.remainder')
        s = self.new(tag + '.slack')
        self.eq(self.add(V, C), self.sum([self.mul(C, out), r, ONE]), tag + '.ceiling')
        self.eq(C, self.sum([r, s, ONE]), tag + '.remainder_bound')
        if not hasattr(self, 'shared_factorial_data'):
            self.shared_factorial_data = []
        self.shared_factorial_data.append(dict(input=n, output=out, rho=rho, C=C,
                                               V=V, remainder=r, slack=s))
        self.macro_log.append(dict(macro='factorial', output=out, n=n, radius=rho,
                                   radius_rule='first_output^2'))
        if not hasattr(self, 'factorial_radix'):
            self.factorial_radix = dict(H=n, rho=rho, numerator=V, factorial=out)
        return out

    def finalize_power_frame(self):
        if self.shared_frame_finalized:
            return
        if not self.power_indices_ready:
            # rho is not requested as a POWER exponent by itself. Its pair
            # supplies both H+rho and t+rho by the exact Pell addition law.
            self.known_exponents = {k for _, k, _, _ in self.pending_powers} | {self.shared_rho}
            self.index_definitions = {out: key for key, out in self.cache.items()}
            _, A, _ = self._scale()
            for n, k, m, tag in self.pending_powers:
                X, Y = self._index(k)
                modulus = self._base(n)
                quotient = self.new(tag + '.quotient')
                self.eq(self.add(X, self.mul(Y, n)),
                        self.sum([self.mul(Y, A), m, self.mul(modulus, quotient)]),
                        tag + '.power_congruence')
                self.macro_log.append(dict(macro='power', output=m, base=n, exponent=k,
                                           shared_scale=True, index_addition=True))
            self.power_indices_ready = True
        # The unchanged finalizer includes the complete actual seed set,
        # including rho, in its simultaneous divisibility product.
        super().finalize_power_frame()


def construct():
    b = SynchronizedExponentBuilder(positive_powers=True)
    src = (parent.ng.UP / 'provenance/upstream/wire_eliminated_source.json').read_bytes()
    source = json.loads(src)
    params = {n: b.new(n + ('0' if n == 't' else ''), 'outer')
              for n in ('t', 'x', 'y', 'M0')}
    params['t'] = b.add(params['t'], TWO)
    t, x, y, M0 = [params[n] for n in ('t', 'x', 'y', 'M0')]
    label = parent.label_majorant(source)
    require(label['exponent'] == 3445908 and label['carrier_exponent'] == 4194304,
            'pinned label majorant')
    carrier = b.power(b.add(t, ONE), b.mul(('c', label['carrier_exponent']), t))
    b.eq(carrier, b.add(M0, ONE), 'projected.carrier')
    u0, r0, ut = [b.new('endpoint.' + n) for n in ('u0', 'r0', 'ut')]
    dt = b.add(b.mul(b.add(t, ONE), y), ONE)
    b.eq(x, b.add(b.add(M0, TWO), b.mul(b.add(y, ONE), u0)), 'endpoint.first_quotient')
    b.eq(y, b.sum([M0, r0, TWO]), 'endpoint.first_remainder')
    b.eq(x, b.add(ONE, b.mul(dt, ut)), 'endpoint.last_quotient')
    bounds = {n: t if i < 4 else y if i < 6 else x for i, n in enumerate(parent.LOCAL_NAMES)}
    columns = {n: b.add(b.new('crt.encoded.' + n), ONE) for n in parent.LOCAL_NAMES}
    index = b.new('crt.encoded_index')
    local = parent.local_majorant(source)
    require(local['exponent'] == 6893253 and local['emitted_exponent'] == 8388608,
            'pinned local majorant')
    R = b.sum([TWO, t, x, y, M0])
    exponent = b.mul(('c', label['carrier_exponent']), t)
    H = b.power(R, exponent)
    T = b.factorial(H)
    B = b.moduli_product(t, T)
    for name in parent.LOCAL_NAMES:
        b.divisible_binomial(columns[name], b.add(bounds[name], ONE), B, 'crt.range.' + name)
    b.eq(b.add(ONE, b.mul(b.add(index, ONE), T)), B, 'crt.canonical_index')
    value = parent.projected_source(b, source, params | columns, index)
    q = b.new('crt.nonnegative_quotient')
    b.eq(value, b.mul(B, q), 'crt.nonnegative_evaluation')
    b.finalize_binomials()
    b.finalize_power_frame()
    interface = dict(t=t, x=x, y=y, M0=M0, carrier=carrier, R=R, exponent=exponent,
                     H=H, T=T, B=B, rho=b.shared_rho, index=index,
                     label_coefficient=4194304, horizon_offset=2)
    return b, src, label, local, interface


def generate():
    b, src, label, local, interface = construct()
    eq, poly, metrics = b.export(hashlib.sha256(src).hexdigest(),
                               'synchronized_exponents_latent_radius', True)
    require((len(b.powers), len(b.shared_bases), len(b.shared_indices), len(b.seed_indices),
             len(b.index_derivations)) == (22, 7, 18, 15, 3), 'complete power/index census')
    raw = reproduce.raw_record(b, label, local)
    raw.update(new_factorial_data=b.shared_factorial_data, rho=b.shared_rho,
               macros=b.macro_log, interface=interface)
    gate = dict(all_variables=b.variables, all_rows=b.rows, gates=b.gates,
                square_difference_gates=b.sqd_ledger)
    files = {'direct/source/equation.json': encoded(eq),
             'direct/source/polynomial.json': encoded(poly),
             'direct/raw_complete.json': encoded(raw),
             'direct/gate_ledger.json': encoded(gate),
             'direct/interface.json': encoded(interface)}
    census = {'source': metrics}
    for cap, name in [(16, 'natural361'), (256, 'natural358')]:
        child, cert, expanded = contract(eq, support_cap=cap)
        require(len(child['variables']) == int(name.removeprefix('natural')), 'measured variable count')
        census[name] = child['metrics']
        for filename, value in [('equation.json', child), ('projection.json', cert),
                                ('polynomial.json', expanded)]:
            files['direct/' + name + '/' + filename] = encoded(value)
    files['direct/CENSUS.json'] = encoded(census)
    return files


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='rebuild and compare without modifying outputs')
    args = parser.parse_args()
    for name, data in generate().items():
        path = ROOT / name
        if args.check:
            require(path.read_bytes() == data, 'deterministic reconstruction: ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    print('PASS: complete source and both quartics ' + ('reconstructed.' if args.check else 'written.'))
