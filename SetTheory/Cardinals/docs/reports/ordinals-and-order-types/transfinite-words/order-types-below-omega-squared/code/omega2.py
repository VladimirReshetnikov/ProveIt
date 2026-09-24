"""Exact symbolic embeddings of ultimately periodic blocks below omega**2.

A token ('f', x) denotes the one-letter word x. A token ('w', D) denotes
an omega-word repeating all members of a nonempty downset D. D is a bitmask.
A Word is a tuple of tokens. Infinite blocks are never finitely truncated.
All public mathematical operations use the label order of a FinitePoset.

See article.tex for proofs of the representation and the decision procedure.
Python 3.10+; standard library only.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product
from typing import Iterable, Iterator, Literal, Sequence, TypeAlias

Token: TypeAlias = tuple[Literal['f', 'w'], int]
Word: TypeAlias = tuple[Token, ...]

@dataclass(frozen=True)
class FinitePoset:
    """pred[y] is the bitmask {x : x <= y}; labels are 0,...,n-1."""
    pred: tuple[int, ...]

    def __post_init__(self) -> None:
        n = len(self.pred)
        full = (1 << n) - 1
        for y, mask in enumerate(self.pred):
            if not isinstance(mask, int) or mask < 0 or mask & ~full:
                raise ValueError('Predecessor masks must be subsets of the label set.')
            if not (mask & (1 << y)):
                raise ValueError('The relation is not reflexive.')
            for x in range(n):
                if mask & (1 << x):
                    if self.pred[x] & ~mask:
                        raise ValueError('The relation is not transitive.')
                    if x != y and self.pred[x] & (1 << y):
                        raise ValueError('The relation is not antisymmetric.')

    @property
    def n(self) -> int:
        return len(self.pred)

    @property
    def full(self) -> int:
        return (1 << self.n) - 1

    def le(self, x: int, y: int) -> bool:
        return bool(self.pred[y] & (1 << x))

    def is_downset(self, mask: int) -> bool:
        return (0 <= mask <= self.full and
                all(not(mask & (1 << x)) or not(self.pred[x] & ~mask)
                    for x in range(self.n)))

    def downsets(self, *, nonempty: bool = False) -> tuple[int, ...]:
        """Ordered by cardinality, hence in an inclusion linear extension."""
        return tuple(sorted((m for m in range(int(nonempty), self.full + 1)
                             if self.is_downset(m)),
                            key=lambda m: (m.bit_count(), m)))

    def maximal_elements(self, downset: int) -> tuple[int, ...]:
        """The maximal elements of a nonempty downset.

        Repeating only these gives an omega-word equivalent to the block that
        repeats all of the downset: B_{Max D} ~ B_D. See Remark 3.2 of
        article.tex. The all-elements block B_D is the official definition
        used by omega() and by embeds(); this method exists so that the
        equivalence can be exercised by the tests.
        """
        if downset == 0 or not self.is_downset(downset):
            raise ValueError('Expected a nonempty downset.')
        return tuple(x for x in range(self.n)
                     if (downset & (1 << x)) and
                     not any(y != x and (downset & (1 << y)) and
                             (self.pred[y] & (1 << x))
                             for y in range(self.n)))

    def upper_mask(self, x: int) -> int:
        """The bitmask {y : x <= y}, the transpose of pred."""
        if not 0 <= x < self.n:
            raise ValueError('Label outside the alphabet.')
        return sum(1 << y for y in range(self.n) if self.pred[y] & (1 << x))

    def validate_word(self, word: Word) -> None:
        for tag, value in word:
            if tag == 'f':
                if not 0 <= value < self.n:
                    raise ValueError('Finite letter outside the alphabet.')
            elif tag == 'w':
                if value == 0 or not self.is_downset(value):
                    raise ValueError('Omega block requires a nonempty downset.')
            else:
                raise ValueError('Unknown token tag.')

    @classmethod
    def antichain(cls, n: int) -> FinitePoset:
        if n < 0:
            raise ValueError('n must be nonnegative.')
        return cls(tuple(1 << i for i in range(n)))

    @classmethod
    def chain(cls, n: int) -> FinitePoset:
        if n < 0:
            raise ValueError('n must be nonnegative.')
        return cls(tuple((1 << (i + 1)) - 1 for i in range(n)))

    @classmethod
    def from_covers(cls, n: int, covers: Iterable[tuple[int, int]]) -> FinitePoset:
        if n < 0:
            raise ValueError('n must be nonnegative.')
        pred = [1 << i for i in range(n)]
        for x, y in covers:
            if not (0 <= x < n and 0 <= y < n):
                raise ValueError('Cover endpoint outside the alphabet.')
            pred[y] |= 1 << x
        for k in range(n):
            for y in range(n):
                if pred[y] & (1 << k):
                    pred[y] |= pred[k]
        return cls(tuple(pred))


def letter(x: int) -> Token:
    return ('f', x)


def omega(downset: int) -> Token:
    return ('w', downset)


def embeds(p: FinitePoset, source: Word, target: Word, *, validate: bool = True) -> bool:
    """Decide source <= target exactly, not by finite expansion.

    The target pointer only moves forward. Finite consumption within a periodic
    omega tail leaves a tail with the same embedding capabilities. Under unit
    cost bit operations, the algorithm uses O(len(source)+len(target)) time and
    O(1) additional memory. Input validation has its own polynomial cost.
    """
    if validate:
        p.validate_word(source)
        p.validate_word(target)
    j = 0
    for s_tag, s_value in source:
        while j < len(target):
            t_tag, t_value = target[j]
            if s_tag == 'f':
                if t_tag == 'f' and p.le(s_value, t_value):
                    j += 1
                    break
                if t_tag == 'w' and (t_value & (1 << s_value)):
                    # Consume finitely many periodic positions; an omega tail remains.
                    break
            elif t_tag == 'w' and not(s_value & ~t_value):
                # An infinite source block uses this target tail cofinally.
                j += 1
                break
            j += 1
        else:
            return False
    return True


def embeds_reference(p: FinitePoset, source: Word, target: Word) -> bool:
    """Nondeterministic dynamic-programming check over all symbolic endpoints.

    Unlike embeds(), this explores every eligible destination block. It shares
    the proved periodic-tail semantics, but not the greedy choice.
    """
    p.validate_word(source)
    p.validate_word(target)
    @lru_cache(maxsize=None)
    def visit(i: int, j: int) -> bool:
        if i == len(source):
            return True
        s_tag, s_value = source[i]
        for k in range(j, len(target)):
            t_tag, t_value = target[k]
            if s_tag == 'f':
                if t_tag == 'f' and p.le(s_value, t_value) and visit(i + 1, k + 1):
                    return True
                if t_tag == 'w' and (t_value & (1 << s_value)) and visit(i + 1, k):
                    return True
            elif t_tag == 'w' and not(s_value & ~t_value) and visit(i + 1, k + 1):
                return True
        return False
    return visit(0, 0)


def ordinal_length(word: Word) -> tuple[int, int]:
    """Return (k,m), representing the ordinal omega*k + m."""
    k = m = 0
    for tag, _ in word:
        if tag == 'f':
            m += 1
        else:
            k += 1
            m = 0
    return k, m


def atom_alphabet(p: FinitePoset, family: Sequence[int]) -> tuple[Token, ...]:
    return tuple(letter(x) for x in range(p.n)) + tuple(omega(d) for d in family)


def all_words(atoms: Sequence[Token], max_length: int) -> Iterator[Word]:
    if max_length < 0:
        raise ValueError('max_length must be nonnegative.')
    for length in range(max_length + 1):
        yield from product(atoms, repeat=length)


def proper_marker_map(p: FinitePoset, d: int, components: Sequence[Word]) -> Word:
    """The product embedding Phi_r, for a newly introduced proper downset d.

    Preconditions not checked here: old omega masks E do not contain d, and all
    components are built from those old masks and finite letters.
    """
    if not components:
        raise ValueError('At least one component is required.')
    if d == 0 or not p.is_downset(d) or d == p.full:
        raise ValueError('The marker must be a nonempty proper downset.')
    c = next(x for x in range(p.n) if not(d & (1 << x)))
    out: Word = ()
    for component in components[:-1]:
        out += component + (letter(c), omega(d))
    return out + components[-1]


def pad_to_limit(p: FinitePoset, word: Word, proper_e: int) -> Word:
    """G(w) = w c Omega_E, with c outside the proper downset E."""
    if proper_e == 0 or not p.is_downset(proper_e) or proper_e == p.full:
        raise ValueError('Padding needs a nonempty proper downset.')
    c = next(x for x in range(p.n) if not(proper_e & (1 << x)))
    return word + (letter(c), omega(proper_e))


def full_marker_map(p: FinitePoset, proper_e: int, components: Sequence[Word]) -> Word:
    """Psi_r: limit-pad every nonfinal component, then append Omega_P.

    Reflection preconditions: all omega blocks in components are proper
    downsets, and proper_e belongs to the old allowed family. The code
    constructs the map; it does not verify these family-level conditions.
    """
    if not components:
        raise ValueError('At least one component is required.')
    out: Word = ()
    for component in components[:-1]:
        out += pad_to_limit(p, component, proper_e) + (omega(p.full),)
    return out + components[-1]


def normalize(word: Word) -> Word:
    """Canonical representative of the mutual-embeddability class.

    Stack-based: on arrival of an omega token, pop the immediately preceding
    finite letters while they belong to its downset. The final finite tail is
    never touched. Two normalized token expressions are mutually embeddable if
    and only if they are identical (Proposition 11.2 of article.tex).
    """
    out: list[Token] = []
    for token in word:
        tag, value = token
        if tag == 'w':
            while out and out[-1][0] == 'f' and (value & (1 << out[-1][1])):
                out.pop()
        out.append(token)
    return tuple(out)


def guard(p: FinitePoset, family: Sequence[int], new: int, word: Word) -> Word:
    """The unified guard map g_D of Theorem 6.5, both cases in one entry point.

    A proper new downset is guarded by a single letter outside it. The full
    downset is guarded by pad_to_limit against an earlier proper member of the
    family. The family-level precondition D not contained in E is checked here.
    """
    if new == 0 or not p.is_downset(new) or new in tuple(family):
        raise ValueError('The new marker must be a new nonempty downset.')
    if any(not (new & ~old) for old in family):
        raise ValueError('An old downset contains the new downset.')
    if new != p.full:
        c = next(x for x in range(p.n) if not (new & (1 << x)))
        return word + (letter(c),)
    proper = next((e for e in family if e != p.full), None)
    if proper is None:
        raise ValueError('The universal marker requires an earlier proper downset.')
    return pad_to_limit(p, word, proper)


def encode_product(p: FinitePoset, family: Sequence[int], new: int,
                   components: Sequence[Word]) -> Word:
    """The unified Phi_m of Theorem 6.5: guard every component, including the last.

    This is the all-guarded variant of Remark 6.6. proper_marker_map and
    full_marker_map implement the unguarded-final-component variant used in
    Sections 5 and 6; both are order embeddings of the same Cartesian power.
    """
    if not components:
        raise ValueError('At least one component is required.')
    out: Word = ()
    for i, component in enumerate(components):
        if i:
            out += (omega(new),)
        out += guard(p, family, new, component)
    return out


def theorem_value(p: FinitePoset, family: Sequence[int] | None = None) -> str:
    """Format the proved maximal order type, using omega instead of Unicode."""
    if p.n == 0:
        if family:
            raise ValueError('An empty alphabet has no nonempty tail downsets.')
        return '1'
    fs = tuple(p.downsets(nonempty=True) if family is None else family)
    if len(set(fs)) != len(fs) or any(d == 0 or not p.is_downset(d) for d in fs):
        raise ValueError('The family must consist of distinct nonempty downsets.')
    if fs == (p.full,):
        return f'omega^(omega^{p.n - 1} + 1)' if p.n > 1 else 'omega^2'
    return f'omega^(omega^{p.n + len(fs) - 1})'


def naturally_labelled_posets(n: int) -> Iterator[FinitePoset]:
    """Enumerate relations whose strict comparisons respect 0<...<n-1.

    Every isomorphism class occurs, generally more than once. This is NOT an
    enumeration of all labelings and NOT an isomorphism-free enumeration.
    """
    if not 0 <= n <= 7:
        raise ValueError('This exhaustive enumerator supports 0 <= n <= 7.')
    edges = tuple(combinations(range(n), 2))
    for mask in range(1 << len(edges)):
        pred = [1 << i for i in range(n)]
        for k, (x, y) in enumerate(edges):
            if mask & (1 << k):
                pred[y] |= 1 << x
        try:
            yield FinitePoset(tuple(pred))
        except ValueError:
            pass


def show_word(word: Word) -> str:
    if not word:
        return 'epsilon'
    return ' '.join(str(v) if t == 'f' else 'Omega{' +
                    ','.join(str(x) for x in range(v.bit_length()) if v & (1 << x)) + '}'
                    for t, v in word)


if __name__ == '__main__':
    for p, name in [(FinitePoset.antichain(2), 'two incomparable letters'),
                    (FinitePoset.chain(2), 'two ordered letters')]:
        print(name, ':', theorem_value(p))
