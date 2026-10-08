"""Exact literal-word DAGs. No hashing assumption and no implicit free reduction."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable

@dataclass(frozen=True)
class Meta:
    length: int
    first: int
    last: int
    reduced: bool

class Grammar:
    """Rules e, t(letter), c(left,right), p(child,nonnegative exponent).

    Power rules are a succinct convenience; ``binary`` eliminates them exactly.
    Node IDs are topological, and node zero is the empty word.
    """
    def __init__(self) -> None:
        self.rules: list[tuple] = [('e',)]
        self.meta: list[Meta] = [Meta(0,0,0,True)]
        self._intern = {('e',):0}

    def _add(self, rule: tuple, meta: Meta) -> int:
        if rule not in self._intern:
            self._intern[rule] = len(self.rules)
            self.rules.append(rule); self.meta.append(meta)
        return self._intern[rule]

    def letter(self, x: int) -> int:
        if type(x) is not int or x == 0:
            raise ValueError('letters are nonzero integers')
        return self._add(('t',x),Meta(1,x,x,True))

    def _node(self, n: int) -> None:
        if type(n) is not int or not 0 <= n < len(self.rules):
            raise ValueError('invalid or forward node reference')

    def concat(self, a: int, b: int) -> int:
        self._node(a); self._node(b)
        if a == 0: return b
        if b == 0: return a
        x,y = self.meta[a],self.meta[b]
        return self._add(('c',a,b),Meta(x.length+y.length,x.first,y.last,
                         x.reduced and y.reduced and x.last != -y.first))

    def power(self, a: int, k: int) -> int:
        self._node(a)
        if type(k) is not int or k < 0: raise ValueError('nonnegative integer power required')
        if k == 0 or a == 0: return 0
        if k == 1: return a
        m = self.meta[a]
        return self._add(('p',a,k),Meta(m.length*k,m.first,m.last,
                                      m.reduced and m.first != -m.last))

    def run(self, a: int, exponent: int) -> int:
        if type(exponent) is not int: raise ValueError('integer exponent required')
        return self.power(self.letter(a if exponent >= 0 else -a),abs(exponent))

    def word(self, xs: Iterable[int]) -> int:
        row=[self.letter(x) for x in xs]
        while len(row)>1:
            row=[self.concat(row[i],row[i+1]) if i+1<len(row) else row[i]
                 for i in range(0,len(row),2)]
        return row[0] if row else 0

    def reachable(self, roots: list[int]) -> list[int]:
        seen=set(); todo=list(roots)
        while todo:
            n=todo.pop(); self._node(n)
            if n in seen or n==0: continue
            seen.add(n); q=self.rules[n]
            if q[0]=='c': todo.extend(q[1:])
            elif q[0]=='p': todo.append(q[1])
        return sorted(seen)

    def validate_roots(self, roots: list[int]) -> None:
        for n in roots:
            self._node(n); m=self.meta[n]
            if not m.reduced or (m.length>1 and m.first == -m.last):
                raise ValueError('roots must be literally freely and cyclically reduced')

    def expand(self, root: int, limit: int=100000) -> list[int]:
        self._node(root)
        if self.meta[root].length > limit: raise ValueError('expansion limit')
        vals={0:[]}
        for n in self.reachable([root]):
            q=self.rules[n]
            vals[n]=([q[1]] if q[0]=='t' else
                     vals[q[1]]+vals[q[2]] if q[0]=='c' else vals[q[1]]*q[2])
        return vals[root]

    def binary(self, roots: list[int]) -> tuple['Grammar',list[int]]:
        """Convert power nodes by binary powering, preserving sharing."""
        out=Grammar(); mp={0:0}
        for n in self.reachable(roots):
            q=self.rules[n]
            if q[0]=='t': mp[n]=out.letter(q[1])
            elif q[0]=='c': mp[n]=out.concat(mp[q[1]],mp[q[2]])
            else:
                k=q[2]; a=mp[q[1]]; acc=0
                while k:
                    if k&1: acc=out.concat(acc,a)
                    k >>= 1
                    if k: a=out.concat(a,a)
                mp[n]=acc
        return out,[mp[n] for n in roots]

    def to_dict(self, roots: list[int]) -> dict:
        return {'version':1,'nodes':[list(q) for q in self.rules],'roots':roots}

    @classmethod
    def from_dict(cls, data: dict) -> tuple['Grammar',list[int]]:
        if set(data)!={'version','nodes','roots'} or type(data['version']) is not int or data['version']!=1:
            raise ValueError('invalid grammar schema')
        nodes=data['nodes']
        if not isinstance(nodes,list) or not nodes or nodes[0]!=['e']:
            raise ValueError('missing empty node')
        out=cls(); mp={0:0}
        for n,q in enumerate(nodes[1:],1):
            if not isinstance(q,list) or not q: raise ValueError('invalid rule')
            if q[0]=='t' and len(q)==2: mp[n]=out.letter(q[1])
            elif q[0] in ('c','p') and len(q)==3:
                inds=q[1:] if q[0]=='c' else q[1:2]
                if any(type(i) is not int or i not in mp for i in inds): raise ValueError('forward reference')
                mp[n]=(out.concat(mp[q[1]],mp[q[2]]) if q[0]=='c' else out.power(mp[q[1]],q[2]))
            else: raise ValueError('invalid rule')
        roots=data['roots']
        if not isinstance(roots,list) or any(type(i) is not int or i not in mp for i in roots):
            raise ValueError('invalid roots')
        return out,[mp[i] for i in roots]
