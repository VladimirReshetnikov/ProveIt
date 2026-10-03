"""Fully emitted, exactly costed fixed-source-horizon SOS frontend.

The polynomial is stored as a sum of squares of sparse degree <=2 integer
polynomials.  This is an ordinary polynomial; no external predicates, power
atoms, integrality atoms, or implicit guards are part of its certificate.
The horizon is a compiler argument, not an unbounded polynomial variable.
"""
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from types import MappingProxyType
from five_binary import BinaryCA, Machine


def polynomial(terms):
    acc = {}
    for coefficient, monomial in terms:
        if type(coefficient) is not int or type(monomial) not in (list, tuple) or any(not nat(i) for i in monomial):
            raise ValueError('polynomial coefficients and variable indices must be exact integers')
        monomial = tuple(sorted(monomial))
        acc[monomial] = acc.get(monomial, 0) + coefficient
    return [(c, mon) for mon, c in sorted(acc.items()) if c]


def nat(x):
    return type(x) is int and x >= 0


@dataclass(frozen=True, slots=True)
class Branch:
    source: str
    target: str
    op: str
    counter: int | None
    delta: int


def branches(machine):
    if not isinstance(machine, Machine):
        raise ValueError('branches require a validated Machine')
    out = []
    for q in sorted(machine.rows):
        r = machine.rows[q]
        if r[0] == 'ADD':
            out.append(Branch(q, r[2], 'ADD', r[1], 1))
        elif r[0] == 'SUB':
            out.extend((Branch(q, r[2], 'DEC', r[1], -1),
                        Branch(q, r[3], 'ZERO', r[1], 0)))
        else:
            out.append(Branch(q, r[1], 'NOP', None, 0))
    return out


class Frontend:
    __slots__ = ('ca', 'h', 'initial_state', 'initial_counters', 'clock', 'real',
                 'branches', 'B', 'control', 'names', 'selectors',
                 'counter_variables', 'theta', 'residuals', '_frozen')

    def __setattr__(self, name, value):
        if getattr(self, '_frozen', False):
            raise AttributeError('a compiled Frontend is immutable')
        object.__setattr__(self, name, value)

    def __delattr__(self, name):
        raise AttributeError('a compiled Frontend is immutable')

    def __init__(self, ca: BinaryCA, horizon: int, initial_state=None,
                 initial_counters=(0, 0), clock=True, nonnegative_real=False):
        if not isinstance(ca, BinaryCA):
            raise ValueError('frontend requires a validated BinaryCA')
        if not nat(horizon) or type(initial_counters) not in (list, tuple) or len(initial_counters) != 2 or not all(map(nat, initial_counters)):
            raise ValueError('horizon and initial counters must be natural integers')
        if type(clock) is not bool or type(nonnegative_real) is not bool:
            raise ValueError('clock and nonnegative_real must be Boolean flags')
        self.ca = ca
        self.h = horizon
        self.initial_state = ca.machine.entry if initial_state is None else initial_state
        ca.machine.validate_configuration(self.initial_state, *initial_counters)
        self.initial_counters = tuple(initial_counters)
        self.clock = clock
        self.real = nonnegative_real
        self.branches = tuple(branches(ca.machine))
        self.B = len(self.branches)
        self.control = MappingProxyType({q: i for i, q in enumerate(ca.states)})
        self.names = []
        self.selectors = []
        self.counter_variables = []
        for t in range(horizon):
            self.selectors.append([self.variable(f'e_{t}_{j}') for j in range(self.B)])
            self.counter_variables.append([self.variable(f'counter_{t+1}_{k}') for k in range(2)])
        self.theta = self.variable('physical_time') if clock else None
        self.residuals = []
        if horizon == 0:
            self.add('halt', [(self.control[self.initial_state]-self.control[ca.machine.halt], ())])
            if clock:
                self.add('clock', [(1, (self.theta,))])
            self._seal()
            return
        for t, e in enumerate(self.selectors):
            self.add(f'{t}.onehot', [(1, (i,)) for i in e] + [(-1, ())])
            if self.real:
                self.add(f'{t}.selector_norm', [(1, (i,i)) for i in e] + [(-1, ())])
            state = [(self.control[b.source], (i,)) for b, i in zip(self.branches,e)]
            if t == 0:
                state.append((-self.control[self.initial_state], ()))
            else:
                state += [(-self.control[b.target], (i,))
                          for b, i in zip(self.branches,self.selectors[t-1])]
            self.add(f'{t}.state', state)
            for k in range(2):
                terms = [(1,(self.counter_variables[t][k],))]
                terms += [(-c, mon) for c, mon in self.old_counter(t,k)]
                terms += [(-b.delta, (i,)) for b,i in zip(self.branches,e) if b.counter == k]
                self.add(f'{t}.counter{k}', terms)
            for j,(b,i) in enumerate(zip(self.branches,e)):
                if b.op == 'ZERO':
                    self.add(f'{t}.zero{j}', [(c, mon+(i,)) for c,mon in self.old_counter(t,b.counter)])
        self.add('halt', [(self.control[b.target],(i,))
                         for b,i in zip(self.branches,self.selectors[-1])]
                 + [(-self.control[ca.machine.halt],())])
        if clock:
            terms = [(1,(self.theta,))]
            for t,e in enumerate(self.selectors):
                for b,i in zip(self.branches,e):
                    if b.op in ('ZERO','NOP'):
                        terms.append((-1,(i,)))
                    else:
                        kappa = (3+2*ca.Z+b.delta-2*ca.K-2*ca.C
                                 -ca.codes['O',b.source]-ca.codes['I',b.source])
                        terms.append((-kappa,(i,)))
                        terms += [(-2*c,mon+(i,)) for c,mon in self.old_counter(t,b.counter)]
            self.add('clock', terms)
        self._seal()

    def _seal(self):
        self.names = tuple(self.names)
        self.selectors = tuple(tuple(row) for row in self.selectors)
        self.counter_variables = tuple(tuple(row) for row in self.counter_variables)
        self.residuals = tuple((label,tuple(terms)) for label,terms in self.residuals)
        self._frozen = True

    def variable(self, name):
        if getattr(self, '_frozen', False):
            raise ValueError('cannot add a variable to a compiled frontend')
        if type(name) is not str or not name or name in self.names:
            raise ValueError('variable names must be unique nonempty strings')
        self.names.append(name)
        return len(self.names)-1

    def old_counter(self, t, k):
        if not nat(t) or t > self.h or type(k) is not int or k not in (0,1):
            raise ValueError('invalid counter layer or index')
        return ([(self.initial_counters[k], ())] if t == 0
                else [(1,(self.counter_variables[t-1][k],))])

    def add(self, label, terms):
        if getattr(self, '_frozen', False):
            raise ValueError('cannot change a compiled frontend')
        if type(label) is not str or not label:
            raise ValueError('residual labels must be nonempty strings')
        self.residuals.append((label, polynomial(terms)))

    def residual_values(self, witness):
        if type(witness) not in (list, tuple):
            raise ValueError('witness must be an exact coordinate list or tuple')
        if len(witness) != len(self.names):
            raise ValueError('wrong witness length')
        if not self.real and not all(map(nat,witness)):
            raise ValueError('witness domain is natural integers')
        if self.real and any(type(x) not in (int, Fraction) or x < 0 for x in witness):
            raise ValueError('exact evaluation of the nonnegative-real polynomial accepts nonnegative int/Fraction coordinates only')
        values = []
        for label, terms in self.residuals:
            total = 0
            for coefficient, monomial in terms:
                term = coefficient
                for index in monomial:
                    term *= witness[index]
                total += term
            values.append((label,total))
        return values

    def evaluate(self,witness):
        return sum(x*x for _,x in self.residual_values(witness))

    def witness(self):
        q = self.initial_state
        a,b = self.initial_counters
        out = [0]*len(self.names)
        time = 0
        for t in range(self.h):
            if q == self.ca.machine.halt:
                return None
            row = self.ca.machine.rows[q]
            op = row[0]
            if op == 'SUB':
                op = 'DEC' if (a,b)[row[1]] else 'ZERO'
            choice = [j for j,x in enumerate(self.branches) if x.source==q and x.op==op]
            if len(choice) != 1:
                raise AssertionError('source is not deterministic')
            out[self.selectors[t][choice[0]]] = 1
            time += self.ca.duration(q,a,b)
            q,a,b = self.ca.machine.step(q,a,b)
            out[self.counter_variables[t][0]],out[self.counter_variables[t][1]] = a,b
        if q != self.ca.machine.halt:
            return None
        if self.clock:
            out[self.theta] = time
        assert self.evaluate(out) == 0
        return out

    def ledger(self):
        z = sum(b.op=='ZERO' for b in self.branches)
        lengths = [len(terms) for _,terms in self.residuals]
        degree = max((2*len(mon) for _,terms in self.residuals for _,mon in terms),default=0)
        return dict(horizon=self.h, branch_count=self.B, zero_branches=z,
                    domain='nonnegative real' if self.real else 'natural integer',
                    witness_variables=len(self.names), squared_residual_slots=len(self.residuals),
                    nonzero_residuals=sum(bool(t) for _,t in self.residuals),
                    polynomial_degree_upper_bound=degree,
                    residual_monomial_occurrences=sum(lengths),
                    expanded_square_ordered_term_occurrence_bound=sum(n*n for n in lengths),
                    exact_clock=self.clock, horizon_is_syntax=True,
                    natural_inputs=list(self.initial_counters))

    def export(self,path):
        obj = dict(format='ordinary polynomial as explicit sum of squares',
                   variables=self.names,
                   residuals=[dict(label=label,terms=[dict(coefficient=c,monomial=list(mon)) for c,mon in terms])
                              for label,terms in self.residuals], ledger=self.ledger())
        Path(path).write_text(json.dumps(obj,separators=(',',':'))+'\n')
        return obj
