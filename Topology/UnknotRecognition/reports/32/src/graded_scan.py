"""Exact bigraded disk-braid scan over F_2, research integration candidate.

SPDX-License-Identifier: MIT-0
Uses the prior report's unchanged geometric composition implementation in vendor/.
This is not a replacement for the maintained fastunknot package. Input size is
expanded braid-word length. Timeout/size exhaustion raises, never decides a knot.
"""
from __future__ import annotations
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from time import perf_counter
import argparse
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'vendor'))
from braid_scan import BraidArc
from radical import Mat, bits, rank_binary, mul, pivot_reduce


@dataclass(frozen=True)
class GObj:
    matching: int
    degree: int
    quantum: int


@dataclass
class Limits:
    max_objects: int = 200_000
    seconds: float | None = 60.0
    started: float = 0.0

    def start(self):
        if type(self.max_objects) is not int or self.max_objects < 1:
            raise ValueError('max_objects must be positive')
        if self.seconds is not None and self.seconds <= 0:
            raise ValueError('seconds must be positive or None')
        self.started = perf_counter()

    def check(self, objects: int | None = None):
        if objects is not None and objects > self.max_objects:
            raise MemoryError('object limit exceeded: no knot verdict')
        if self.seconds is not None and perf_counter() - self.started > self.seconds:
            raise TimeoutError('time limit exceeded: no knot verdict')


def validate_word(strands: int, word: list[int]) -> None:
    if type(strands) is not int or strands < 1:
        raise ValueError('strands must be a positive integer')
    if any(type(x) is not int or not 1 <= abs(x) < strands for x in word):
        raise ValueError('invalid Artin generator')


def check_grading(d: Mat, alg: BraidArc, *, square: bool = False) -> int:
    count = 0
    for j, col in enumerate(d.cols):
        a = d.src[j]
        for i, f in col.items():
            b = d.src[i]
            if b.degree != a.degree + 1:
                raise ArithmeticError('incorrect homological grading')
            if alg.weights(a.matching, b.matching, f) != {b.quantum-a.quantum}:
                raise ArithmeticError('incorrect absolute quantum grading')
            count += 1
    if square and not mul(d, d, alg).is_zero():
        raise ArithmeticError('d squared is nonzero')
    return count


def occupancy(d: Mat) -> int:
    return max(Counter((o.degree, o.quantum) for o in d.src).values(), default=0)


def profile(d: Mat, alg: BraidArc) -> list:
    c = Counter((alg.pairs[o.matching], o.degree, o.quantum) for o in d.src)
    return [[list(map(list,a)), h, q, m] for (a,h,q),m in sorted(c.items())]


def residue_multiplicities(d: Mat) -> Counter:
    """Independent graded residue ranks predict every minimal multiplicity."""
    groups = defaultdict(list)
    for j,o in enumerate(d.src): groups[o.matching,o.degree,o.quantum].append(j)
    ranks = {}
    for (a,h,q),ids in groups.items():
        target = {i:r for r,i in enumerate(groups.get((a,h+1,q),()))}
        columns = []
        for j in ids:
            columns.append(sum(1<<target[i] for i,f in d.cols[j].items()
                               if i in target and f&1))
        ranks[a,h,q] = rank_binary(columns)
    result = Counter()
    for key,ids in groups.items():
        a,h,q = key
        b = len(ids)-ranks[key]-ranks.get((a,h-1,q),0)
        if b < 0: raise ArithmeticError('invalid residue complex')
        if b: result[key] = b
    return result


def check_disk(d: Mat, alg: BraidArc, strands: int) -> None:
    order = list(range(strands))+list(range(2*strands-1,strands-1,-1))
    position = {p:i for i,p in enumerate(order)}
    for mid in {o.matching for o in d.src}:
        pairs = alg.pairs[mid]
        if sorted(x for pair in pairs for x in pair) != list(range(2*strands)):
            raise ArithmeticError('wrong disk boundary')
        chords = [tuple(sorted((position[a],position[b]))) for a,b in pairs]
        if any(a<c<b<e or c<a<e<b for k,(a,b) in enumerate(chords)
               for c,e in chords[k+1:]):
            raise ArithmeticError('crossing boundary pairing')


def attach(d: Mat, alg: BraidArc, slots: tuple, positive: bool, limits: Limits) -> Mat:
    """Tensor one crossing, then deloop; do not prune before cancellation."""
    obs = []
    index = {}
    def smoothing(i): return 1-i if positive else i
    for j, o in enumerate(d.src):
        for i in (0,1):
            g = alg.glue(o.matching, smoothing(i), slots)
            for labels in product((0,1), repeat=g.closed):
                limits.check(len(obs)+1)
                index[j,i,labels] = len(obs)
                obs.append(GObj(g.matching, o.degree+i,
                                o.quantum+i+g.closed-2*sum(labels)))
    cols = [{} for _ in obs]
    def put(a,b,f):
        value = cols[a].get(b,0)^f
        if value: cols[a][b] = value
        else: cols[a].pop(b,None)
    for j, o in enumerate(d.src):
        limits.check()
        for ls,lt,v in alg.crossing_entries(o.matching,o.matching,1,
                                           smoothing(0),smoothing(1),slots)[2]:
            put(index[j,0,ls],index[j,1,lt],v)
        for k, f in d.cols[j].items():
            for i in (0,1):
                for ls,lt,v in alg.crossing_entries(o.matching,d.src[k].matching,f,
                                                   smoothing(i),smoothing(i),slots)[2]:
                    put(index[j,i,ls],index[k,i,lt],v)
    return Mat(tuple(obs),tuple(obs),cols)


def reduce_fifo(d: Mat, alg: BraidArc, *, rebuild: bool = False,
                reverse: bool = False) -> tuple[Mat,dict]:
    """Local adjacency elimination; rebuild=True is a same-pivot audit control.

    Only genuine homogeneous identity pivots are cancelled. Queue entries are
    deduplicated while pending. Stale entries are checked before any mutation.
    """
    obs = d.src
    out = [dict(c) for c in d.cols]
    inc = [set() for _ in obs]
    active = [True]*len(obs)
    for j,col in enumerate(out):
        for i in col: inc[i].add(j)
    queue = deque()
    pending = set()
    pushes = pairs = pivots = rebuild_scanned = 0
    max_degree = max((max(len(out[j]),len(inc[j])) for j in range(len(obs))),default=0)
    def scalar(a,b,f):
        return f == 1 and obs[a].matching == obs[b].matching and obs[a].quantum == obs[b].quantum
    def enqueue(a,b):
        nonlocal pushes
        if (a,b) not in pending:
            queue.append((a,b)); pending.add((a,b)); pushes += 1
    for j in (range(len(obs)-1,-1,-1) if reverse else range(len(obs))):
        for i,f in sorted(out[j].items(), reverse=reverse):
            if scalar(j,i,f): enqueue(j,i)
    while queue:
        alg.check()
        b,c = queue.popleft(); pending.remove((b,c))
        if not active[b] or not active[c] or not scalar(b,c,out[b].get(c,0)):
            continue
        if rebuild:
            # Identical algebra and FIFO queue; only reverse-index maintenance
            # is deliberately replaced by a complete scan, for paired ablation.
            inc = [set() for _ in obs]
            for j,col in enumerate(out):
                rebuild_scanned += len(col)+1
                for i in col: inc[i].add(j)
        left = sorted(inc[c]-{b})
        right = [(i,out[b][i]) for i in sorted(out[b]) if i != c]
        for a in left:
            f = out[a][c]
            for z,g in right:
                pairs += 1
                value = out[a].get(z,0) ^ alg.compose(obs[a].matching,obs[b].matching,
                                                     obs[z].matching,f,g)
                if value:
                    out[a][z] = value; inc[z].add(a)
                    if scalar(a,z,value): enqueue(a,z)
                else:
                    out[a].pop(z,None); inc[z].discard(a)
                max_degree = max(max_degree,len(out[a]),len(inc[z]))
        # Delete every incidence, not just the pivot row and column.
        for v in (b,c):
            for j in list(inc[v]): out[j].pop(v,None)
            for i in list(out[v]): inc[i].discard(v)
            inc[v].clear(); out[v].clear(); active[v] = False
        pivots += 1
    ids = [i for i,a in enumerate(active) if a]
    index = {v:i for i,v in enumerate(ids)}
    objects = tuple(obs[i] for i in ids)
    result = Mat(objects,objects,[{index[i]:f for i,f in out[j].items()} for j in ids])
    stats = dict(pivots=pivots,update_pairs=pairs,queue_pushes=pushes,
                 max_incidence=max_degree,rebuild_scanned=rebuild_scanned)
    return result,stats


def rebase(d: Mat, old: BraidArc, rename: dict[int,int], limits: Limits) -> tuple[Mat,BraidArc]:
    """Canonicalize boundary labels and transport dot indices; drop old caches."""
    alg = BraidArc(); alg.check = limits.check
    mapping = {}
    for o in d.src:
        if o.matching not in mapping:
            pairs = tuple(sorted(tuple(sorted((rename[a],rename[b]))) for a,b in old.pairs[o.matching]))
            mapping[o.matching] = alg.intern(pairs)
    objects = tuple(GObj(mapping[o.matching],o.degree,o.quantum) for o in d.src)
    perms = {}
    cols = []
    for j,col in enumerate(d.cols):
        newcol = {}
        for i,f in col.items():
            key = (d.src[j].matching,d.src[i].matching)
            if key not in perms:
                owner,c = old.basis(*key)
                newowner,cc = alg.basis(mapping[key[0]],mapping[key[1]])
                if c != cc: raise ArithmeticError('relabelled overlay differs')
                perm = [None]*c
                for p,k in owner.items(): perm[k] = newowner[rename[p]]
                perms[key] = perm
            perm = perms[key]
            value = 0
            for mask in bits(f):
                transported = sum(1<<perm[k] for k in bits(mask))
                value ^= 1<<transported
            newcol[i] = value
        cols.append(newcol)
    return Mat(objects,objects,cols),alg


def close_bigraded(d: Mat, alg: BraidArc, strands: int, word: list[int],
                   limits: Limits) -> list[list[int]]:
    """Actual closure functor, graded before rank computation."""
    closure = alg.intern(tuple((j,strands+j) for j in range(strands)))
    neg = sum(x<0 for x in word); shift = len(word)-3*neg
    groups = defaultdict(list)
    grades = {}
    for j,o in enumerate(d.src):
        c = alg.basis(closure,o.matching)[1]
        for mask in range(1<<c):
            key = (o.degree-neg,o.quantum+shift+c-2*mask.bit_count())
            groups[key].append((j,mask)); grades[j,mask] = key
            limits.check(len(grades))
    index = {key:{b:i for i,b in enumerate(bs)} for key,bs in groups.items()}
    ranks = {}
    for key,bs in groups.items():
        limits.check()
        target = (key[0]+1,key[1]); columns = []
        for j,mask in bs:
            value = 0
            for i,f in d.cols[j].items():
                result = alg.compose(closure,d.src[j].matching,d.src[i].matching,1<<mask,f)
                for t in bits(result):
                    if grades[i,t] != target:
                        raise ArithmeticError('closure violates quantum grading')
                    value ^= 1<<index[target][i,t]
            columns.append(value)
        ranks[key] = rank_binary(columns)
    answer = []
    for (h,q),bs in sorted(groups.items()):
        b = len(bs)-ranks[h,q]-ranks.get((h-1,q),0)
        if b < 0: raise ArithmeticError('invalid homology dimension')
        if b: answer.append([h,q,b])
    return answer


def braid_components(strands: int, word: list[int]) -> int:
    p = list(range(strands))
    for x in word:
        j = abs(x)-1; p[j],p[j+1] = p[j+1],p[j]
    unseen = set(range(strands)); count = 0
    while unseen:
        count += 1; j = next(iter(unseen))
        while j in unseen:
            unseen.remove(j); j = p[j]
    return count


def scan(strands: int, word: list[int], *, reducer: str = 'local', audit: bool = False,
         record_profiles: bool = False, limits: Limits | None = None) -> dict:
    validate_word(strands,word)
    if reducer not in ('local','rebuild','reverse','reference'):
        raise ValueError('unknown reducer')
    limits = limits or Limits(); limits.start(); limits.check(strands)
    alg = BraidArc(); alg.check = limits.check
    ident = alg.intern(tuple((j,strands+j) for j in range(strands)))
    objects = (GObj(ident,0,0),); d = Mat(objects,objects,[{}]); trace = []
    checks = 0; calls = 0
    for step,x in enumerate(word,1):
        j = abs(x)-1
        slots = (strands+j,strands+j+1,2*strands+1,2*strands)
        d = attach(d,alg,slots,x>0,limits)
        checks += check_grading(d,alg,square=audit)
        before = len(d.src); before_occ = occupancy(d); nnz = d.nnz
        predicted = residue_multiplicities(d) if audit else None
        started = perf_counter()
        if reducer == 'reference':
            d = pivot_reduce(d,alg); stats = {}
        else:
            d,stats = reduce_fifo(d,alg,rebuild=reducer=='rebuild',reverse=reducer=='reverse')
        elapsed = perf_counter()-started
        checks += check_grading(d,alg,square=audit)
        if audit and predicted != Counter((o.matching,o.degree,o.quantum) for o in d.src):
            raise ArithmeticError('graded residue multiplicity mismatch')
        rec = dict(step=step,pre_objects=before,pre_occupancy=before_occ,pre_entries=nnz,
                   objects=len(d.src),occupancy=occupancy(d),entries=d.nnz,
                   reduce_seconds=elapsed,**stats)
        rename = {k:k for k in range(2*strands) if k not in (strands+j,strands+j+1)}
        rename[2*strands] = strands+j; rename[2*strands+1] = strands+j+1
        calls += alg.calls
        d,alg = rebase(d,alg,rename,limits)
        if audit:
            checks += check_grading(d,alg,square=True)
            check_disk(d,alg,strands)
        if record_profiles: rec['profile'] = profile(d,alg)
        trace.append(rec)
    homology = close_bigraded(d,alg,strands,word,limits)
    total = sum(row[2] for row in homology)
    components = braid_components(strands,word)
    verdict = ('UNKNOT' if total==2 else 'KNOTTED') if components==1 else 'LINK'
    return dict(strands=strands,word=word,components=components,bigraded_homology=homology,
                unreduced_rank=total,verdict=verdict,trace=trace,
                checked_entries=checks,composition_calls=calls+alg.calls,
                seconds=perf_counter()-limits.started)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--strands',type=int,required=True)
    p.add_argument('--word',required=True,help='JSON array of signed Artin generators')
    p.add_argument('--reducer',choices=('local','rebuild','reverse','reference'),default='local')
    p.add_argument('--audit',action='store_true')
    p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--max-objects',type=int,default=200_000)
    a = p.parse_args()
    try:
        word = json.loads(a.word)
        if not isinstance(word,list): raise ValueError('word must be a JSON list')
        result = scan(a.strands,word,reducer=a.reducer,audit=a.audit,
                      limits=Limits(a.max_objects,a.seconds))
        print(json.dumps(result,indent=2))
    except (ValueError,TimeoutError,MemoryError) as exc:
        print(json.dumps({'status':'NO_VERDICT','error':str(exc)})); return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
