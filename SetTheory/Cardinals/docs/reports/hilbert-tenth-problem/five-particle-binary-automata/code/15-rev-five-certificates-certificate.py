"""Exact fixed-source-horizon SOS certificates for guarded two-counter machines.

No opaque callable guards. No CA simulation proof is supplied by this module.
Source tables are fully snapshotted and checked using their finite guard cells.
The represented horizon is syntax, not an unbounded polynomial input.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from types import MappingProxyType
import json
from pathlib import Path


def nat(x):
    return type(x) is int and x >= 0


def freeze_guard(root):
    """Validate/snapshot a finite AST without recursion; shared subtrees are fine."""
    pending, active, values = [(root,False)], set(), []
    while pending:
        g, leaving = pending.pop()
        if type(g) is bool:
            values.append(g)
            continue
        if not leaving:
            if type(g) not in (list,tuple) or not g or type(g[0]) is not str:
                raise ValueError('guard must be a finite Boolean AST')
            if id(g) in active:
                raise ValueError('guard must be finite and acyclic')
            tag=g[0]
            if tag in ('eq','gt'):
                if len(g)!=3 or type(g[1]) is not int or g[1] not in (0,1) or not nat(g[2]):
                    raise ValueError('guard atoms require counter 0/1 and natural threshold')
                values.append(tuple(g))
                continue
            if tag=='not' and len(g)==2:
                children=(g[1],)
            elif tag in ('and','or'):
                children=g[1:]
            else:
                raise ValueError('unknown or malformed guard expression')
            active.add(id(g));pending.append((g,True))
            pending.extend((x,False) for x in reversed(children))
        else:
            n=len(g)-1
            children=tuple(values[-n:]) if n else ()
            if n:
                del values[-n:]
            values.append((g[0],)+children)
            active.remove(id(g))
    return values[0]


def guard_value(root,c):
    pending, values=[(root,False)],[]
    while pending:
        g,leaving=pending.pop()
        if type(g) is bool:
            values.append(g)
        elif g[0] in ('eq','gt'):
            values.append(c[g[1]]==g[2] if g[0]=='eq' else c[g[1]]>g[2])
        elif not leaving:
            pending.append((g,True));pending.extend((x,False) for x in reversed(g[1:]))
        else:
            n=len(g)-1
            children=values[-n:] if n else []
            if n:
                del values[-n:]
            values.append(not children[0] if g[0]=='not' else all(children) if g[0]=='and' else any(children))
    return values[0]


def atoms(root):
    pending,out=[root],[]
    while pending:
        g=pending.pop()
        if type(g) is bool:
            continue
        if g[0] in ('eq','gt'):
            out.append(g)
        else:
            pending.extend(reversed(g[1:]))
    return tuple(out)


@dataclass(frozen=True, slots=True, init=False)
class Branch:
    name: str
    source: str
    target: str
    counter: int
    delta: int
    guard: object

    def __init__(self,name,source,target,counter,delta,guard):
        if hasattr(self,'name'):
            raise AttributeError('Branch snapshots cannot be reinitialized')
        if any(type(x) is not str for x in (name,source,target)):
            raise ValueError('branch names and controls must be exact strings')
        if type(counter) is not int or counter not in (0,1):
            raise ValueError('counter must be exactly 0 or 1')
        if type(delta) is not int or delta not in (-1,0,1):
            raise ValueError('delta must be exactly -1, 0 or 1')
        guard=freeze_guard(guard)
        for key,value in (('name',name),('source',source),('target',target),('counter',counter),('delta',delta),('guard',guard)):
            object.__setattr__(self,key,value)


@dataclass(frozen=True, slots=True, init=False)
class CellBranch:
    original: int
    classes: tuple

    def __init__(self,original,classes):
        if hasattr(self,'original'):
            raise AttributeError('CellBranch snapshots cannot be reinitialized')
        if not nat(original) or type(classes) is not tuple or len(classes)!=2 or not all(map(nat,classes)):
            raise ValueError('invalid normalized branch cell')
        object.__setattr__(self,'original',original)
        object.__setattr__(self,'classes',classes)


@dataclass(frozen=True, slots=True, init=False)
class Machine:
    controls: tuple
    branches: tuple
    halt: str
    J: int
    cells: tuple
    control_codes: object

    def __init__(self, controls, branches, halt, J):
        if hasattr(self,'controls'):
            raise AttributeError('Machine snapshots cannot be reinitialized')
        if type(controls) not in (list, tuple) or not controls or any(type(q) is not str for q in controls):
            raise ValueError('controls must be a nonempty finite list/tuple of strings')
        controls = tuple(controls)
        if len(set(controls)) != len(controls) or halt not in controls or type(halt) is not str:
            raise ValueError('controls must be distinct and contain the halt control')
        if type(branches) not in (list, tuple) or any(type(b) is not Branch for b in branches):
            raise ValueError('branches must be a list/tuple of validated Branch objects')
        branches = tuple(branches)
        if len({b.name for b in branches}) != len(branches):
            raise ValueError('branch names must be distinct')
        if not nat(J):
            raise ValueError('J must be an exact natural cutoff')
        for b in branches:
            if b.source not in controls or b.target not in controls or b.source == halt:
                raise ValueError('unknown control or outgoing halt branch')
            for _, k, threshold in atoms(b.guard):
                # Sufficient syntactic criterion. Deliberately conservative under cancellation.
                if J < max(threshold, threshold + (b.delta if k == b.counter else 0)):
                    raise ValueError('J must capture every domain and shifted image threshold')
        reps = tuple(product(range(J+2), repeat=2))
        for q in controls:
            for c in reps:
                outgoing = [b for b in branches if b.source == q and guard_value(b.guard, c)]
                if len(outgoing) > 1:
                    raise ValueError('overlapping original branch domains')
                for b in outgoing:
                    if c[b.counter] + b.delta < 0:
                        raise ValueError('guard permits negative output')
                incoming = []
                for b in branches:
                    if b.target != q:
                        continue
                    old = list(c)
                    old[b.counter] -= b.delta
                    if min(old) >= 0 and guard_value(b.guard, old):
                        incoming.append(b)
                if len(incoming) > 1:
                    raise ValueError('overlapping original branch images')
        cells = tuple(CellBranch(i, c) for i, b in enumerate(branches)
                      for c in reps if guard_value(b.guard, c))
        object.__setattr__(self, 'controls', controls)
        object.__setattr__(self, 'branches', branches)
        object.__setattr__(self, 'halt', halt)
        object.__setattr__(self, 'J', J)
        object.__setattr__(self, 'cells', cells)
        object.__setattr__(self, 'control_codes', MappingProxyType({q:i for i,q in enumerate(controls)}))

    def validate_id(self, q, c):
        if type(q) is not str or q not in self.controls or type(c) not in (tuple, list) or len(c) != 2 or not all(map(nat,c)):
            raise ValueError('ID requires a known control and two exact natural counters')

    def transition(self, q, c):
        self.validate_id(q,c)
        enabled = [(i,b) for i,b in enumerate(self.branches) if b.source == q and guard_value(b.guard,c)]
        if not enabled:
            return None
        if len(enabled) != 1:
            raise RuntimeError('validated machine lost determinism')
        i,b = enabled[0]
        new = list(c)
        new[b.counter] += b.delta
        return i,b.target,tuple(new)

    def geometry(self):
        m = len(self.controls)
        p = sum(b.delta != 0 for b in self.branches)
        a = len(self.branches)-p
        D = 2*m+4*p
        S = 2*D+2
        Z = 40*D+60+2*self.J
        return dict(m=m,p=p,a=a,J=self.J,D=D,S=S,Z=Z)

    def duration(self, original, counters):
        if not nat(original) or original >= len(self.branches):
            raise ValueError('invalid original branch index')
        if type(counters) not in (list,tuple) or len(counters) != 2 or not all(map(nat,counters)):
            raise ValueError('duration requires two natural counters')
        b = self.branches[original]
        if not guard_value(b.guard,counters):
            raise ValueError('duration requested outside branch domain')
        g = self.geometry()
        return 1 if b.delta == 0 else 3+2*(g['Z']+counters[b.counter])+b.delta-4*g['S']


def polynomial(terms):
    acc = {}
    for coefficient, monomial in terms:
        if type(coefficient) is not int or type(monomial) not in (tuple,list) or any(not nat(i) for i in monomial):
            raise ValueError('sparse terms require integer coefficients and natural variable indices')
        mon = tuple(sorted(monomial))
        acc[mon] = acc.get(mon,0)+coefficient
    return tuple((c,mon) for mon,c in sorted(acc.items()) if c)


class Certificate:
    __slots__ = ('machine','H','initial_state','initial_counters','clock','real','names','selectors',
                 'counters','slacks','theta','residuals','_sealed')

    def __setattr__(self, name, value):
        if getattr(self,'_sealed',False):
            raise AttributeError('compiled certificates are immutable')
        object.__setattr__(self,name,value)

    def __delattr__(self,name):
        raise AttributeError('compiled certificates are immutable')

    def __init__(self, machine, horizon, initial_state, initial_counters, *, clock=False, nonnegative_real=False):
        if type(machine) is not Machine:
            raise ValueError('certificate requires a validated immutable Machine')
        if not nat(horizon) or type(clock) is not bool or type(nonnegative_real) is not bool:
            raise ValueError('horizon must be natural and flags exactly Boolean')
        machine.validate_id(initial_state,initial_counters)
        self.machine,self.H = machine,horizon
        self.initial_state,self.initial_counters = initial_state,tuple(initial_counters)
        self.clock,self.real = clock,nonnegative_real
        self.names,self.selectors,self.counters,self.slacks,self.residuals = [],[],[],[],[]
        B,J = len(machine.cells),machine.J
        for t in range(horizon):
            self.selectors.append(tuple(self._var(f'e_{t}_{b}') for b in range(B)))
            self.counters.append(tuple(self._var(f'c_{t+1}_{k}') for k in (0,1)))
            self.slacks.append(tuple(tuple(self._var(f's_{t}_{b}_{k}') if cell.classes[k] == J+1 else None
                                           for k in (0,1)) for b,cell in enumerate(machine.cells)))
        self.theta = self._var('Theta') if clock else None
        code = machine.control_codes
        if horizon == 0:
            self._add('terminal',[(code[initial_state]-code[machine.halt],())])
        for t,selectors in enumerate(self.selectors):
            self._add(f'{t}.onehot',[(1,(e,)) for e in selectors]+[(-1,())])
            if self.real:
                self._add(f'{t}.norm',[(1,(e,e)) for e in selectors]+[(-1,())])
            state = [(code[machine.branches[c.original].source],(e,)) for c,e in zip(machine.cells,selectors)]
            if t == 0:
                state.append((-code[initial_state],()))
            else:
                state.extend((-code[machine.branches[c.original].target],(e,)) for c,e in zip(machine.cells,self.selectors[t-1]))
            self._add(f'{t}.state',state)
            for k in (0,1):
                terms = [(1,(self.counters[t][k],))] + [(-a,mon) for a,mon in self._old(t,k)]
                terms += [(-machine.branches[c.original].delta,(e,)) for c,e in zip(machine.cells,selectors)
                          if machine.branches[c.original].counter == k]
                self._add(f'{t}.counter{k}',terms)
            for b,(cell,e) in enumerate(zip(machine.cells,selectors)):
                for k in (0,1):
                    terms = [(a,mon+(e,)) for a,mon in self._old(t,k)]
                    terms.append((-cell.classes[k],(e,)))
                    if self.slacks[t][b][k] is not None:
                        terms.append((-1,(self.slacks[t][b][k],)))
                    self._add(f'{t}.class{b}.{k}',terms)
        if horizon:
            self._add('terminal',[(code[machine.branches[c.original].target],(e,))
                                 for c,e in zip(machine.cells,self.selectors[-1])]+[(-code[machine.halt],())])
        if clock:
            g = machine.geometry()
            terms = [(1,(self.theta,))]
            for t,selectors in enumerate(self.selectors):
                for cell,e in zip(machine.cells,selectors):
                    b = machine.branches[cell.original]
                    kappa = 1 if b.delta == 0 else 3+2*g['Z']+b.delta-4*g['S']
                    terms.append((-kappa,(e,)))
                    if b.delta:
                        terms.extend((-2*a,mon+(e,)) for a,mon in self._old(t,b.counter))
            self._add('clock',terms)
        self.names = tuple(self.names)
        self.selectors,self.counters,self.slacks = tuple(self.selectors),tuple(self.counters),tuple(self.slacks)
        self.residuals = tuple(self.residuals)
        self._sealed = True

    def _var(self,name):
        self.names.append(name)
        return len(self.names)-1

    def _old(self,t,k):
        return [(self.initial_counters[k],())] if t == 0 else [(1,(self.counters[t-1][k],))]

    def _add(self,label,terms):
        self.residuals.append((label,polynomial(terms)))

    def residual_values(self,w):
        if type(w) not in (tuple,list) or len(w) != len(self.names):
            raise ValueError('witness must have exactly the emitted number of coordinates')
        if self.real:
            if any(type(x) not in (int,Fraction) or x < 0 for x in w):
                raise ValueError('exact real-orthant evaluation accepts nonnegative int/Fraction, never float or bool')
        elif not all(map(nat,w)):
            raise ValueError('witness domain is exact natural integers')
        values = []
        for label,terms in self.residuals:
            total = 0
            for a,mon in terms:
                value = a
                for i in mon:
                    value *= w[i]
                total += value
            values.append((label,total))
        return tuple(values)

    def evaluate(self,w):
        return sum(v*v for _,v in self.residual_values(w))

    def expanded(self):
        return polynomial((a*b,ma+mb) for _,terms in self.residuals for a,ma in terms for b,mb in terms)

    def witness(self):
        q,c = self.initial_state,self.initial_counters
        w,theta = [0]*len(self.names),0
        J = self.machine.J
        for t in range(self.H):
            result = self.machine.transition(q,c)
            if result is None:
                return None
            original,qnew,cnew = result
            cls = tuple(min(v,J+1) for v in c)
            choices = [i for i,cell in enumerate(self.machine.cells) if cell.original == original and cell.classes == cls]
            if len(choices) != 1:
                raise RuntimeError('normalization did not yield a unique enabled cell')
            b = choices[0]
            w[self.selectors[t][b]] = 1
            for k in (0,1):
                w[self.counters[t][k]] = cnew[k]
                s = self.slacks[t][b][k]
                if s is not None:
                    w[s] = c[k]-J-1
            theta += self.machine.duration(original,c)
            q,c = qnew,cnew
        if q != self.machine.halt:
            return None
        if self.clock:
            w[self.theta] = theta
        if self.evaluate(w) != 0:
            raise RuntimeError('constructed witness did not satisfy emitted residuals')
        return tuple(w)

    def ledger(self):
        B = len(self.machine.cells)
        r = sum(k == self.machine.J+1 for c in self.machine.cells for k in c.classes)
        B_nonzero = sum(self.machine.branches[c.original].delta != 0 for c in self.machine.cells)
        lengths = [len(terms) for _,terms in self.residuals]
        degree = max((2*len(mon) for _,terms in self.residuals for _,mon in terms),default=0)
        g = self.machine.geometry()
        kappa = max([1]+[3+2*g['Z']+b.delta-4*g['S'] for b in self.machine.branches if b.delta])
        M = max(self.initial_counters)
        coefficient_height=max((abs(a) for _,terms in self.residuals for a,_ in terms),default=0)
        clock_height=self.H*(kappa+2*M)+self.H*(self.H-1)
        coordinate_height=max(1,M+self.H,clock_height if self.clock else 0)
        return dict(horizon=self.H,horizon_is_syntax=True,original_branches=len(self.machine.branches),
                    normalization_cells_examined=len(self.machine.branches)*(self.machine.J+2)**2,
                    normalized_branches=B,normalized_nonzero_branches=B_nonzero,tail_occurrences=r,
                    variables=len(self.names),residual_slots=len(self.residuals),nonzero_residuals=sum(bool(t) for _,t in self.residuals),
                    domain='nonnegative real' if self.real else 'natural integer',
                    natural_external_inputs=list(self.initial_counters),degree_upper_bound=degree,
                    residual_monomial_occurrences=sum(lengths),expanded_ordered_occurrence_bound=sum(n*n for n in lengths),
                    residual_coefficient_height=coefficient_height,expanded_coefficient_height_bound=sum(n*n for n in lengths)*coefficient_height**2,
                    total_witness_coordinate_height_bound=coordinate_height,total_witness_coordinate_bit_bound=coordinate_height.bit_length(),
                    counter_and_slack_height=max(1,M+self.H),clock_height=self.H*(kappa+2*M)+self.H*(self.H-1),
                    conditional_CA_spatial_diameter_bound=2*g['Z']+sum(self.initial_counters)+self.H,
                    exact_clock=self.clock,compiler_geometry=g,CA_correctness_not_asserted_by_this_module=True)

    def export(self,path):
        obj = dict(format='ordinary integer polynomial as explicit sum of squared degree-at-most-two residuals',
                   variables=list(self.names),residuals=[dict(label=label,terms=[dict(coefficient=a,monomial=list(mon)) for a,mon in terms])
                                                       for label,terms in self.residuals],ledger=self.ledger(),
                   normalized_cells=[dict(original=c.original,classes=list(c.classes)) for c in self.machine.cells])
        Path(path).write_text(json.dumps(obj,indent=2)+'\n')
        return obj


def _json_guard(root):
    pending,active,values=[(root,False)],set(),[]
    while pending:
        obj,leaving=pending.pop()
        if not leaving:
            if type(obj) is not dict or any(type(k) is not str for k in obj) or type(obj.get('op')) is not str:
                raise ValueError('JSON guard must be an object with a known op')
            if id(obj) in active:
                raise ValueError('JSON guard must be finite and acyclic')
            op=obj['op']
            if op=='true' and set(obj)=={'op'}:
                values.append(True);continue
            if op in ('eq','gt') and set(obj)=={'op','counter','value'}:
                values.append(freeze_guard((op,obj['counter'],obj['value'])));continue
            if op=='not' and set(obj)=={'op','arg'}:
                children=(obj['arg'],)
            elif op in ('and','or') and set(obj)=={'op','args'} and type(obj['args']) is list:
                children=obj['args']
            else:
                raise ValueError('unknown, missing, or extraneous JSON guard fields')
            active.add(id(obj));pending.append((obj,True))
            pending.extend((x,False) for x in reversed(children))
        else:
            n=1 if obj['op']=='not' else len(obj['args'])
            children=tuple(values[-n:]) if n else ()
            if n:
                del values[-n:]
            values.append((obj['op'],)+children)
            active.remove(id(obj))
    return values[0]


def load_machine(obj):
    """Read a strict snapshot of reversible-two-counter-v1; return (machine,start)."""
    keys = {'schema','controls','start','halt','class_cut','branches'}
    if type(obj) is not dict or any(type(k) is not str for k in obj) or set(obj) != keys or type(obj['schema']) is not str or obj['schema'] != 'reversible-two-counter-v1':
        raise ValueError('expected exact reversible-two-counter-v1 schema fields')
    if type(obj['controls']) is not list:
        raise ValueError('JSON controls must be an array')
    if type(obj['branches']) is not list:
        raise ValueError('JSON branches must be an array')
    branches = []
    for row in obj['branches']:
        if type(row) is not dict or any(type(k) is not str for k in row) or set(row) != {'name','source','target','side','delta','guard'}:
            raise ValueError('unexpected branch schema fields')
        if type(row['side']) is not int or row['side'] not in (-1,1):
            raise ValueError('side must be exactly -1 or +1')
        branches.append(Branch(row['name'],row['source'],row['target'],0 if row['side']==-1 else 1,row['delta'],_json_guard(row['guard'])))
    machine = Machine(obj['controls'],branches,obj['halt'],obj['class_cut'])
    if type(obj['start']) is not str or obj['start'] not in machine.controls:
        raise ValueError('start must be a named control')
    return machine,obj['start']


def _main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source')
    parser.add_argument('horizon',type=int)
    parser.add_argument('--left',type=int,default=0)
    parser.add_argument('--right',type=int,default=0)
    parser.add_argument('--clock',action='store_true')
    parser.add_argument('--real',action='store_true')
    parser.add_argument('--output',default='certificate.json')
    args = parser.parse_args()
    machine,start = load_machine(json.loads(Path(args.source).read_text()))
    certificate = Certificate(machine,args.horizon,start,(args.left,args.right),clock=args.clock,nonnegative_real=args.real)
    certificate.export(args.output)
    witness = certificate.witness()
    Path(args.output+'.witness.json').write_text(json.dumps(witness)+'\n')
    print(json.dumps(dict(ledger=certificate.ledger(),accepted=witness is not None),indent=2))


if __name__ == '__main__':
    _main()
