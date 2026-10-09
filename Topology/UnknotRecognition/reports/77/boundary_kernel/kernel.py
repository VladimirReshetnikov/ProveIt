"""Small Heisenberg quotients of a marked closed orientable surface group.

All arithmetic is exact. NONTRIVIAL is sound for arbitrary surface words.
UNDETECTED means contractible ONLY after a separate source check establishes
that the free homotopy class has a simple closed representative traversed once.
No function in this module returns an UNKNOT verdict.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
import json
from typing import Any, Iterable, Sequence


def exponent_mod(exponent: int | str, modulus: int) -> int:
    """Read an integer or signed 0b-prefixed binary string without expansion."""
    if modulus <= 0:
        raise ValueError('positive modulus required')
    if type(exponent) is int:
        return exponent % modulus
    if not isinstance(exponent, str):
        raise TypeError('exponent must be int or signed binary string')
    sign, text = 1, exponent
    if text.startswith(('-', '+')):
        if text[0] == '-':
            sign = -1
        text = text[1:]
    if not text.startswith('0b') or len(text) == 2:
        raise ValueError('string exponent must be signed 0b-prefixed binary')
    out = 0
    for digit in text[2:]:
        if digit not in '01':
            raise ValueError('invalid binary exponent')
        out = (2*out + (digit == '1')) % modulus
    return (sign*out) % modulus


@dataclass(frozen=True)
class Signature:
    vector: tuple[int, ...]  # a_1,b_1,...,a_g,b_g
    area: int


class Kernel:
    """H_g(q): coordinate modulus q, central modulus g (g >= 2).

    q=g is the smallest scalar detector. For transport_safe=True, q=2g
    when g is even and q=g otherwise. The latter admits all symplectic
    changes of generators; the even-genus narrow kernel does not.
    """
    def __init__(self, genus: int, transport_safe: bool = False):
        if type(genus) is not int or genus < 2:
            raise ValueError('Heisenberg kernel requires integer genus >= 2')
        self.g = genus
        self.q = 2*genus if transport_safe and genus % 2 == 0 else genus
        self.exponent = genus if genus % 2 else 2*genus
        self.transport_safe = bool(transport_safe)

    def zero(self) -> Signature:
        return Signature((0,)*(2*self.g), 0)

    def validate(self, a: Signature) -> None:
        if not isinstance(a, Signature) or not isinstance(a.vector, tuple) or len(a.vector) != 2*self.g:
            raise ValueError('wrong signature dimension')
        if any(type(v) is not int or not 0 <= v < self.q for v in a.vector):
            raise ValueError('noncanonical vector residue')
        if type(a.area) is not int or not 0 <= a.area < self.g:
            raise ValueError('noncanonical central residue')

    def generator(self, index: int, sign: int = 1) -> Signature:
        if type(index) is not int or not 0 <= index < 2*self.g or sign not in (-1, 1):
            raise ValueError('invalid generator')
        v = [0]*(2*self.g)
        v[index] = sign % self.q
        return Signature(tuple(v), 0)

    def cocycle(self, a: Sequence[int], b: Sequence[int]) -> int:
        return sum(a[2*i]*b[2*i+1] for i in range(self.g)) % self.g

    def multiply(self, a: Signature, b: Signature) -> Signature:
        return Signature(tuple((u+v) % self.q for u,v in zip(a.vector,b.vector)),
                         (a.area+b.area+self.cocycle(a.vector,b.vector)) % self.g)

    def inverse(self, a: Signature) -> Signature:
        return Signature(tuple(-v % self.q for v in a.vector),
                         (-a.area+self.cocycle(a.vector,a.vector)) % self.g)

    def power(self, a: Signature, k: int | str) -> Signature:
        # Every group element has order dividing exponent; read only that residue.
        r = exponent_mod(k, self.exponent)
        return Signature(tuple(r*v % self.q for v in a.vector),
                         (r*a.area+(r*(r-1)//2)*self.cocycle(a.vector,a.vector)) % self.g)

    def literal(self, word: Iterable[int]) -> Signature:
        out = self.zero()
        for letter in word:
            if type(letter) is not int or letter == 0:
                raise ValueError('letters are nonzero signed 1-based indices')
            out = self.multiply(out, self.generator(abs(letter)-1, 1 if letter > 0 else -1))
        return out


class SLP:
    """A topologically ordered straight-line program, with inverse and power rules.

    Rules: ('id',), ('gen', signed_1based_index), ('cat', left, right),
    ('inv', child), ('pow', child, int_or_signed_binary_string).
    """
    def __init__(self, rules: Sequence[Sequence[Any]], root: int | None = None):
        self.rules = tuple(tuple(rule) for rule in rules)
        self.root = len(self.rules)-1 if root is None else root
        if not self.rules or type(self.root) is not int or not 0 <= self.root < len(self.rules):
            raise ValueError('invalid root')
        for i, r in enumerate(self.rules):
            if not r or r[0] not in ('id','gen','cat','inv','pow'):
                raise ValueError('unknown rule')
            count = {'id':1,'gen':2,'cat':3,'inv':2,'pow':3}[r[0]]
            if len(r) != count:
                raise ValueError('wrong rule arity')
            if r[0] == 'gen' and (type(r[1]) is not int or r[1] == 0):
                raise ValueError('invalid generator letter')
            args = r[1:3] if r[0] == 'cat' else r[1:2] if r[0] in ('inv','pow') else ()
            if any(type(j) is not int or not 0 <= j < i for j in args):
                raise ValueError('references must point to earlier nodes')
            if r[0] == 'pow':
                exponent_mod(r[2], 1)  # validates even when residue is unused

    def payload(self) -> dict[str, Any]:
        rules = []
        for rule in self.rules:
            r = list(rule)
            if r[0] == 'pow' and type(r[2]) is int:
                r[2] = ('-' if r[2] < 0 else '')+'0b'+format(abs(r[2]),'b')
            rules.append(r)
        return {'rules':rules, 'root':self.root}

    def digest(self) -> str:
        data = json.dumps(self.payload(), sort_keys=True, separators=(',',':')).encode()
        return sha256(data).hexdigest()

    def evaluate(self, kernel: Kernel, images: Sequence[Signature] | None = None,
                 all_nodes: bool = False) -> Signature | list[Signature]:
        # Do not build all 2g dense generator vectors: that would cost g^2
        # even for a one-rule word. Default generators are created on demand.
        # A supplied image table is separately validated and charged as input.
        if images is not None:
            if len(images) != 2*kernel.g:
                raise ValueError('wrong generator image count')
            for value in images:
                kernel.validate(value)
        values: list[Signature] = []
        for r in self.rules:
            op = r[0]
            if op == 'id': value = kernel.zero()
            elif op == 'gen':
                j = abs(r[1])-1
                if j >= 2*kernel.g: raise ValueError('generator outside surface presentation')
                if images is None:
                    value = kernel.generator(j, 1 if r[1] > 0 else -1)
                else:
                    value = images[j] if r[1] > 0 else kernel.inverse(images[j])
            elif op == 'cat': value = kernel.multiply(values[r[1]], values[r[2]])
            elif op == 'inv': value = kernel.inverse(values[r[1]])
            else: value = kernel.power(values[r[1]], r[2])
            values.append(value)
        return values if all_nodes else values[self.root]

    def expand(self, cap: int = 100000) -> list[int]:
        """Literal test oracle only; production evaluation never calls this."""
        values: list[list[int]] = []
        for r in self.rules:
            if r[0] == 'id': v = []
            elif r[0] == 'gen': v = [r[1]]
            elif r[0] == 'cat':
                if len(values[r[1]])+len(values[r[2]]) > cap: raise OverflowError('expansion cap')
                v = values[r[1]]+values[r[2]]
            elif r[0] == 'inv': v = [-x for x in reversed(values[r[1]])]
            else:
                e = r[2] if type(r[2]) is int else int(r[2],2)
                u = values[r[1]]
                if len(u)*abs(e) > cap: raise OverflowError('expansion cap')
                v = (u if e >= 0 else [-x for x in reversed(u)])*abs(e)
            if len(v) > cap: raise OverflowError('expansion cap')
            values.append(v)
        return values[self.root]


class Builder:
    def __init__(self): self.rules: list[tuple[Any,...]] = []
    def add(self, *rule: Any) -> int:
        self.rules.append(tuple(rule)); return len(self.rules)-1
    def cat(self, a: int, b: int) -> int: return self.add('cat',a,b)
    def inv(self, a: int) -> int: return self.add('inv',a)
    def comm(self, a: int, b: int) -> int:
        return self.cat(self.cat(a,b),self.cat(self.inv(a),self.inv(b)))
    def word(self, letters: Iterable[int]) -> int:
        level = [self.add('gen',x) for x in letters]
        if not level: return self.add('id')
        while len(level)>1:
            level = [self.cat(level[i],level[i+1]) if i+1<len(level) else level[i]
                     for i in range(0,len(level),2)]
        return level[0]
    def build(self, root: int | None = None) -> SLP: return SLP(self.rules,root)


def observe(slp: SLP, genus: int, transport_safe: bool = False) -> dict[str, Any]:
    k = Kernel(genus, transport_safe)
    s = slp.evaluate(k)
    assert isinstance(s, Signature)
    nonzero_homology = any(s.vector)
    nontrivial = nonzero_homology or s.area != 0
    return {'schema':'boundary-heisenberg-observation-v1', 'genus':genus,
            'coordinate_modulus':k.q, 'word_sha256':slp.digest(),
            'vector':list(s.vector), 'area':s.area,
            'status':'NONTRIVIAL' if nontrivial else 'UNDETECTED',
            'simple_curve_consequence':
                'essential nonseparating' if nonzero_homology else
                'essential separating' if s.area else 'contractible',
            'complementary_genera_if_simple':None if nonzero_homology else
                sorted((s.area, genus-s.area)),
            'requires_external_simple_source_for_consequence':True}


def certificate(slp: SLP, genus: int, transport_safe: bool = False) -> dict[str, Any]:
    out = observe(slp,genus,transport_safe)
    out['word'] = slp.payload()
    return out


def check_symplectic_images(kernel: Kernel, images: Sequence[Signature]) -> bool:
    if len(images) != 2*kernel.g: return False
    try:
        for s in images: kernel.validate(s)
    except (TypeError,ValueError): return False
    q = kernel.q
    for i,u in enumerate(images):
        for j,v in enumerate(images):
            pairing = sum(u.vector[2*h]*v.vector[2*h+1]-u.vector[2*h+1]*v.vector[2*h]
                          for h in range(kernel.g)) % q
            target = (1 if j == i+1 and i%2==0 else -1 if i == j+1 and j%2==0 else 0) % q
            if pairing != target: return False
    return True


class TransportPlan:
    """Check a safe symplectic image tuple once, then transport many values.

    This compiles finite algebraic data; it does not certify a geometric map.
    Generator images are copied into an immutable tuple of canonical signatures.
    """
    __slots__ = ('_kernel', '_images')

    def __init__(self, kernel: Kernel, images: Sequence[Signature]):
        if kernel.g % 2 == 0 and kernel.q == kernel.g:
            raise ValueError('even-genus narrow quotient is not transport-safe')
        if not check_symplectic_images(kernel, images):
            raise ValueError('generator images are not symplectic')
        self._kernel = Kernel(kernel.g, True)
        self._images = tuple(Signature(tuple(s.vector), s.area) for s in images)

    def apply(self, signature: Signature) -> Signature:
        kernel, images = self._kernel, self._images
        kernel.validate(signature)
        # Canonical section: all b powers first, then all a powers (zero area).
        out = kernel.zero()
        for j in list(range(1, 2*kernel.g, 2))+list(range(0, 2*kernel.g, 2)):
            out = kernel.multiply(out, kernel.power(images[j], signature.vector[j]))
        return kernel.multiply(out, Signature((0,)*(2*kernel.g), signature.area))


def transport(kernel: Kernel, signature: Signature, images: Sequence[Signature]) -> Signature:
    """Convenience one-shot transport; use TransportPlan to amortize image checking."""
    return TransportPlan(kernel, images).apply(signature)
