"""Indexed finite-horizon quartic SOS certificates for primitive counter rows.

The literal source is snapshotted once. Certificate construction and its ledger
allocate no horizon-sized variable, residual, or polynomial arrays. Small explicit
SOS/expanded exports are separately bounded. No callable guards are accepted.
"""
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from types import MappingProxyType
import hashlib
import json


def nat(x):
    return type(x) is int and x >= 0


def need(ok, message):
    if not ok:
        raise ValueError(message)


def obj(x, keys):
    need(type(x) is dict and all(type(k) is str for k in x) and set(x) == set(keys), 'exact object keys required')


def nodup(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, 'duplicate JSON key')
        out[k] = v
    return out


@dataclass(frozen=True, slots=True, init=False)
class Branch:
    name: str
    source: str
    target: str
    counter: int
    delta: int
    kind: str
    tested: object

    def __init__(self, name, source, target, counter, delta, guard):
        if hasattr(self, 'name'):
            raise AttributeError('branch snapshot cannot be reinitialized')
        need(all(type(v) is str for v in (name, source, target)), 'exact strings required')
        need(type(counter) is int and counter in (0, 1), 'counter must be exactly 0 or 1')
        need(type(delta) is int and delta in (-1, 0, 1), 'delta must be exactly -1, 0 or 1')
        need(type(guard) is dict and type(guard.get('op')) is str, 'finite primitive JSON guard required')
        op = guard['op']
        tested = None
        if op == 'true':
            obj(guard, ('op',))
            need(delta in (0, 1), 'unguarded decrement forbidden')
            kind = 'A' if delta == 0 else 'I'
        else:
            obj(guard, ('op', 'counter', 'value'))
            need(op in ('eq', 'gt'), 'only primitive zero/positive guards accepted')
            tested = guard['counter']
            need(type(tested) is int and tested in (0, 1) and type(guard['value']) is int and guard['value'] == 0,
                 'primitive guards test exactly zero on counter 0 or 1')
            if delta == -1:
                need(op == 'gt' and tested == counter, 'decrement must test its updated counter positive')
                kind = 'D'
            else:
                need(delta == 0, 'increment must be unguarded')
                kind = 'Z' if op == 'eq' else 'P'
        for key, value in (('name', name), ('source', source), ('target', target), ('counter', counter),
                           ('delta', delta), ('kind', kind), ('tested', tested)):
            object.__setattr__(self, key, value)

    def enabled(self, counters):
        need(type(counters) in (list, tuple) and len(counters) == 2 and all(nat(c) for c in counters), 'exact natural counters required')
        return self._enabled(counters)

    def _enabled(self, counters):
        if self.kind in ('A', 'I'):
            return True
        return counters[self.tested] == 0 if self.kind == 'Z' else counters[self.tested] > 0

    def mask(self, image=False):
        need(type(image) is bool, 'image flag must be exactly Boolean')
        # Four *bits*, never normalized branch/cell records. Each bit represents
        # one zero/positive domain class. These masks decide all-natural overlap.
        mask = 0
        for a in (0, 1):
            for b in (0, 1):
                c = [a, b]
                if image:
                    c[self.counter] -= self.delta
                if min(c) >= 0 and self._enabled(c):
                    mask |= 1 << (2*a+b)
        return mask


@dataclass(frozen=True, slots=True, init=False)
class Machine:
    controls: tuple
    branches: tuple
    start: str
    halt: str
    J: int
    codes: object
    outgoing: object
    zero: tuple
    positive: tuple
    moving: tuple
    reversible: bool
    no_incoming_start: bool

    def __init__(self, controls, branches, start, halt, J=0, *, require_reversible=False):
        if hasattr(self, 'controls'):
            raise AttributeError('machine snapshot cannot be reinitialized')
        need(type(require_reversible) is bool, 'require_reversible must be Boolean')
        need(type(controls) in (tuple, list) and controls and all(type(q) is str for q in controls), 'finite nonempty controls required')
        controls = tuple(controls)
        codes = {q: i for i, q in enumerate(controls)}
        need(len(codes) == len(controls), 'duplicate control')
        need(type(start) is str and type(halt) is str and start in codes and halt in codes, 'known start/halt required')
        need(nat(J), 'class cut must be an exact natural')
        need(type(branches) in (list, tuple) and all(type(b) is Branch for b in branches), 'validated primitive branches required')
        branches = tuple(branches)
        need(len({b.name for b in branches}) == len(branches), 'duplicate branch name')
        outs, domain_masks, image_masks = {}, {}, {}
        reversible = True
        for i, b in enumerate(branches):
            need(b.source in codes and b.target in codes and b.source != halt, 'unknown control or halt exit')
            d, im = b.mask(), b.mask(True)
            need(not (domain_masks.get(b.source, 0) & d), 'overlapping branch domains')
            domain_masks[b.source] = domain_masks.get(b.source, 0) | d
            if image_masks.get(b.target, 0) & im:
                reversible = False
            image_masks[b.target] = image_masks.get(b.target, 0) | im
            outs.setdefault(b.source, []).append(i)
        need(not require_reversible or reversible, 'overlapping branch images')
        values = dict(controls=controls, branches=branches, start=start, halt=halt, J=J,
                      codes=MappingProxyType(codes), outgoing=MappingProxyType({q: tuple(v) for q, v in outs.items()}),
                      zero=tuple(i for i,b in enumerate(branches) if b.kind == 'Z'),
                      positive=tuple(tuple(i for i,b in enumerate(branches) if b.kind == 'P' and b.tested == k) for k in (0,1)),
                      moving=tuple(tuple(i for i,b in enumerate(branches) if b.delta and b.counter == k) for k in (0,1)),
                      reversible=reversible, no_incoming_start=start not in image_masks)
        for key, value in values.items():
            object.__setattr__(self, key, value)

    def validate_id(self, q, c):
        need(type(q) is str and q in self.codes and type(c) in (list, tuple) and len(c) == 2 and all(nat(x) for x in c),
             'ID requires known control and exactly two natural integers')

    def transition(self, q, c):
        self.validate_id(q, c)
        for i in self.outgoing.get(q, ()):
            b = self.branches[i]
            if b.enabled(c):
                new = list(c)
                new[b.counter] += b.delta
                return i, b.target, tuple(new)
        return None

    def geometry(self):
        m, p = len(self.controls), sum(map(len, self.moving))
        D = 2*m+4*p
        return dict(m=m, p=p, a=len(self.branches)-p, J=self.J, D=D, S=2*D+2, Z=40*D+60+2*self.J)

    def kappa(self, b):
        need(type(b) is Branch, 'validated primitive Branch required')
        if not b.delta:
            return 1
        g = self.geometry()
        return 3+2*g['Z']+b.delta-4*g['S']

    def duration(self, i, counters):
        need(nat(i) and i < len(self.branches), 'invalid branch index')
        need(type(counters) in (list, tuple) and len(counters) == 2 and all(nat(c) for c in counters), 'natural counters required')
        b = self.branches[i]
        need(b.enabled(counters), 'duration outside branch domain')
        return self.kappa(b)+(2*counters[b.counter] if b.delta else 0)


def load_machine(data, *, require_reversible=False):
    obj(data, ('schema','controls','start','halt','class_cut','branches'))
    need(type(data['schema']) is str and data['schema'] == 'reversible-two-counter-v1', 'source schema mismatch')
    need(type(data['controls']) is list and type(data['branches']) is list, 'JSON arrays required')
    branches = []
    for r in data['branches']:
        obj(r, ('name','source','target','side','delta','guard'))
        need(type(r['side']) is int and r['side'] in (-1,1), 'side must be exactly -1 or 1')
        branches.append(Branch(r['name'],r['source'],r['target'],(r['side']+1)//2,r['delta'],r['guard']))
    return Machine(data['controls'], branches, data['start'], data['halt'], data['class_cut'], require_reversible=require_reversible)


def read_machine(path, *, require_reversible=False):
    data = Path(path).read_bytes()
    return load_machine(json.loads(data, object_pairs_hook=nodup), require_reversible=require_reversible), hashlib.sha256(data).hexdigest()


def polynomial(terms):
    acc = {}
    for a, mon in terms:
        need(type(a) is int and type(mon) is tuple and all(nat(i) for i in mon), 'invalid polynomial term')
        mon = tuple(sorted(mon))
        acc[mon] = acc.get(mon, 0)+a
    return tuple((a,mon) for mon,a in sorted(acc.items()) if a)


@dataclass(frozen=True, slots=True, init=False)
class Certificate:
    machine: Machine
    H: int
    initial_state: str
    initial_counters: tuple
    clock: bool
    real: bool

    def __init__(self, machine, horizon, initial_state, initial_counters, *, clock=False, nonnegative_real=False):
        if hasattr(self, 'machine'):
            raise AttributeError('certificate cannot be reinitialized')
        need(type(machine) is Machine, 'validated immutable machine required')
        need(nat(horizon) and type(clock) is bool and type(nonnegative_real) is bool, 'exact natural horizon and Boolean flags required')
        machine.validate_id(initial_state, initial_counters)
        for key,value in dict(machine=machine,H=horizon,initial_state=initial_state,initial_counters=tuple(initial_counters),clock=clock,real=nonnegative_real).items():
            object.__setattr__(self,key,value)

    @property
    def B(self):
        return len(self.machine.branches)

    @property
    def width(self):
        return self.B+4

    @property
    def nvars(self):
        return self.H*self.width+int(self.clock)

    @property
    def layer_rows(self):
        return 6+len(self.machine.zero)+int(self.real)

    @property
    def nrows(self):
        return self.H*self.layer_rows+1+int(self.clock)

    def _step(self, t):
        need(nat(t) and t < self.H, 'invalid layer index')

    def selector(self,t,i):
        self._step(t)
        need(nat(i) and i < self.B, 'invalid branch index')
        return t*self.width+i

    def z(self,t,k):
        self._step(t)
        need(type(k) is int and k in (0,1), 'invalid counter index')
        return t*self.width+self.B+k

    def offset(self,t,k):
        self._step(t)
        need(type(k) is int and k in (0,1), 'invalid counter index')
        return t*self.width+self.B+2+k

    def name(self,i):
        need(nat(i) and i < self.nvars, 'invalid variable index')
        if i == self.H*self.width:
            return 'Theta'
        t,j = divmod(i,self.width)
        if j < self.B:
            return f'e_{t}_{j}'
        return f'z_{t+1}_{j-self.B}' if j < self.B+2 else f'b_{t}_{j-self.B-2}'

    def _old(self,t,k):
        if t == 0:
            yield self.initial_counters[k], ()
        else:
            yield 1, (self.z(t-1,k),)
            yield 1, (self.offset(t-1,k),)

    def describe_row(self,i):
        need(nat(i) and i < self.nrows, 'invalid residual index')
        if i == self.H*self.layer_rows:
            return 'terminal', None, None
        if i == self.H*self.layer_rows+1:
            return 'clock', None, None
        t,j = divmod(i,self.layer_rows)
        if j == 0: return 'onehot',t,None
        if j == 1: return 'state',t,None
        if j in (2,3): return 'counter',t,j-2
        if j in (4,5): return 'offset',t,j-4
        if j < 6+len(self.machine.zero): return 'zero',t,self.machine.zero[j-6]
        return 'norm',t,None

    def iter_raw_terms(self,i):
        """Yield all written terms of one row, including zero coefficients.

        This generator never builds a universal row list or expands a square.
        """
        kind,t,k = self.describe_row(i)
        m = self.machine
        if kind in ('onehot','norm'):
            for b in range(self.B):
                e = self.selector(t,b)
                yield 1, (e,e) if kind == 'norm' else (e,)
            yield -1, ()
        elif kind == 'state':
            for b,r in enumerate(m.branches):
                yield m.codes[r.source], (self.selector(t,b),)
            if t == 0:
                yield -m.codes[self.initial_state], ()
            else:
                for b,r in enumerate(m.branches):
                    yield -m.codes[r.target], (self.selector(t-1,b),)
        elif kind == 'counter':
            yield 1, (self.z(t,k),)
            yield 1, (self.offset(t,k),)
            for a,mon in self._old(t,k):
                yield -a, mon
            for b in m.moving[k]:
                yield -m.branches[b].delta, (self.selector(t,b),)
        elif kind == 'offset':
            yield 1, (self.offset(t,k),)
            for b in m.positive[k]:
                yield -1, (self.selector(t,b),)
        elif kind == 'zero':
            e = self.selector(t,k)
            yield 1, (e,self.z(t,m.branches[k].tested))
        elif kind == 'terminal':
            if self.H == 0:
                yield m.codes[self.initial_state]-m.codes[m.halt], ()
            else:
                for b,r in enumerate(m.branches):
                    yield m.codes[r.target], (self.selector(self.H-1,b),)
                yield -m.codes[m.halt], ()
        elif kind == 'clock':
            yield 1, (self.H*self.width,)
            for t in range(self.H):
                for b,r in enumerate(m.branches):
                    e = self.selector(t,b)
                    yield -m.kappa(r), (e,)
                    if r.delta:
                        for a,mon in self._old(t,r.counter):
                            yield -2*a, mon+(e,)

    def row(self,i,*,max_terms=100000):
        need(nat(max_terms), 'exact natural row limit required')
        terms = []
        for term in self.iter_raw_terms(i):
            if len(terms) == max_terms:
                raise ValueError('row materialization limit exceeded; use iter_raw_terms')
            terms.append(term)
        return self.describe_row(i), polynomial(terms)

    def ledger(self):
        """Closed-form exact collected row statistics, O(B), independent of H."""
        m,H,B = self.machine,self.H,self.B
        Z,P,M = len(m.zero),sum(map(len,m.positive)),sum(map(len,m.moving))
        ns = sum(m.codes[b.source] != 0 for b in m.branches)
        nt = sum(m.codes[b.target] != 0 for b in m.branches)
        lengths = []  # (multiplicity, collected length), O(1) categories
        def add(n,L):
            if n: lengths.append((n,L))
        if H:
            add(H,B+1)
            if self.real: add(H,B+1)
            add(1,ns+int(m.codes[self.initial_state] != 0))
            add(H-1,ns+nt)
            for k in (0,1):
                mk,pk = len(m.moving[k]),len(m.positive[k])
                add(1,mk+2+int(self.initial_counters[k] != 0))
                add(H-1,mk+4)
                add(H,pk+1)
            add(H*Z,1)
            add(1,nt+int(m.codes[m.halt] != 0))
            raw = H*(3*B+M+P+Z+11)
            if self.real: raw += H*(B+1)
        else:
            add(1,int(self.initial_state != m.halt))
            raw = 1
        if self.clock:
            add(1,1+H*B+2*max(0,H-1)*M)
            raw += 1+H*(B+2*M)-(M if H else 0)
        collected = sum(n*L for n,L in lengths)
        ordered = sum(n*L*L for n,L in lengths)
        max_input = max(self.initial_counters)
        kappa = max([1]+[m.kappa(b) for b in m.branches if b.delta])
        C = max(1,len(m.controls)-1,max_input,kappa+2*max_input if self.clock else 1)
        clock_height = H*(kappa+2*max_input)+H*(H-1)
        height = max(1,max_input+H,clock_height if self.clock else 0)
        return dict(format='indexed shared-offset primitive SOS family',horizon=H,horizon_is_syntax=True,
                    initial_state=self.initial_state,initial_counters=list(self.initial_counters),external_inputs_not_witnesses=True,
                    original_branches=B,zero_test_rows=Z,positive_test_rows=P,moving_rows=M,
                    variables=self.nvars,squared_residual_slots=self.nrows,degree_upper_bound=4,
                    raw_residual_term_slots=raw,collected_residual_monomials=collected,
                    expanded_ordered_product_occurrences=ordered,
                    nonzero_residuals=sum(n for n,L in lengths if L),
                    residual_coefficient_height_bound=C,expanded_coefficient_height_bound=ordered*C*C,
                    witness_domain='nonnegative real orthant' if self.real else 'natural integers',
                    exact_clock=self.clock,paid_selector_norm=self.real,core_variables_per_layer=B+4,
                    core_squares_per_layer=6+Z,core_raw_term_slope=3*B+M+P+Z+11,
                    core_raw_term_intercept=(0 if H else 1),clock_raw_term_slope=B+2*M,
                    clock_raw_term_intercept=(1-M if H else 1),
                    actual_counters_and_stored_z_height=max_input+H,offset_height=1,
                    clock_height=clock_height,witness_coordinate_height_bound=height,witness_coordinate_bit_bound=height.bit_length(),
                    conditional_CA_spatial_diameter_bound=2*m.geometry()['Z']+sum(self.initial_counters)+H,
                    compiler_geometry=m.geometry(),reversible_source=m.reversible,no_incoming_start=m.no_incoming_start,
                    construction_materializes_horizon_polynomial=False,CA_correctness_not_asserted_by_this_module=True)

    def _validate_witness(self,w):
        need(type(w) in (tuple,list) and len(w) == self.nvars, 'wrong witness dimension')
        if self.real:
            need(all(type(v) in (int,Fraction) and v >= 0 for v in w), 'exact nonnegative int/Fraction required; no bool/float')
        else:
            need(all(nat(v) for v in w), 'exact natural integer witnesses required')

    def residual_values(self,w):
        self._validate_witness(w)
        for i in range(self.nrows):
            total = 0
            for a,mon in self.iter_raw_terms(i):
                for j in mon: a *= w[j]
                total += a
            yield self.describe_row(i),total

    def evaluate(self,w):
        return sum(v*v for _,v in self.residual_values(w))

    def witness(self,*,max_variables=10000):
        need(nat(max_variables) and self.nvars <= max_variables, 'witness materialization limit exceeded')
        w = [0]*self.nvars
        q,c,theta = self.initial_state,self.initial_counters,0
        for t in range(self.H):
            step = self.machine.transition(q,c)
            if step is None: return None
            b,qnew,cnew = step
            r = self.machine.branches[b]
            w[self.selector(t,b)] = 1
            for k in (0,1):
                offset = int(r.kind == 'P' and r.tested == k)
                w[self.offset(t,k)] = offset
                w[self.z(t,k)] = cnew[k]-offset
            theta += self.machine.duration(b,c)
            q,c = qnew,cnew
        if q != self.machine.halt: return None
        if self.clock: w[-1] = theta
        need(self.evaluate(w) == 0, 'internal witness construction error')
        return tuple(w)

    def materialize(self,*,max_variables=10000,max_terms=100000):
        need(nat(max_variables) and nat(max_terms), 'exact natural materialization limits required')
        ledger = self.ledger()
        need(self.nvars <= max_variables and ledger['raw_residual_term_slots'] <= max_terms,
             'explicit SOS export exceeds bounds; indexed object and ledger remain available')
        rows = tuple(self.row(i,max_terms=max_terms) for i in range(self.nrows))
        return dict(format='fully materialized ordinary integer polynomial as SOS residuals',
                    variables=tuple(self.name(i) for i in range(self.nvars)),rows=rows,ledger=ledger)

    def expanded(self,*,max_ordered_products=1000000,max_variables=10000,max_terms=100000):
        need(nat(max_ordered_products), 'exact natural expansion limit required')
        need(self.ledger()['expanded_ordered_product_occurrences'] <= max_ordered_products,
             'full polynomial expansion exceeds ordered-product bound')
        data = self.materialize(max_variables=max_variables,max_terms=max_terms)
        return polynomial((a*b,ma+mb) for _,terms in data['rows'] for a,ma in terms for b,mb in terms)

    def export(self,path,*,include_expanded=False,max_variables=10000,max_terms=100000,max_ordered_products=1000000):
        need(type(include_expanded) is bool, 'include_expanded must be Boolean')
        data = self.materialize(max_variables=max_variables,max_terms=max_terms)
        if include_expanded:
            data['expanded_polynomial'] = self.expanded(max_variables=max_variables,max_terms=max_terms,max_ordered_products=max_ordered_products)
        Path(path).write_text(json.dumps(data,indent=2)+'\n')
        return data


def main():
    import argparse
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source');p.add_argument('horizon',type=int)
    p.add_argument('--left',type=int,default=0);p.add_argument('--right',type=int,default=0)
    p.add_argument('--clock',action='store_true');p.add_argument('--real',action='store_true')
    p.add_argument('--require-reversible',action='store_true')
    p.add_argument('--ledger-output');p.add_argument('--export-small')
    args=p.parse_args()
    machine,sha = read_machine(args.source,require_reversible=args.require_reversible)
    c=Certificate(machine,args.horizon,machine.start,(args.left,args.right),clock=args.clock,nonnegative_real=args.real)
    ledger=dict(source_sha256=sha,**c.ledger())
    if args.ledger_output: Path(args.ledger_output).write_text(json.dumps(ledger,indent=2)+'\n')
    if args.export_small: c.export(args.export_small,include_expanded=True)
    print(json.dumps(ledger,indent=2))

if __name__ == '__main__': main()
