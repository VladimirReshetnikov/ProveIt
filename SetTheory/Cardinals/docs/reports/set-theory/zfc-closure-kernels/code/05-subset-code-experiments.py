"""Finite regressions for the new bound-absorption proof, not schema verification."""
from __future__ import annotations
import json
import random
from pathlib import Path
from kernel import closure, Hole, evaluate


def require(condition: bool, detail: object = '') -> None:
    if not condition: raise AssertionError(detail)

def bits(n: int):
    while n:
        low = n & -n; yield low.bit_length()-1; n -= low

def submasks(n: int):
    x = n
    while True:
        yield x
        if x == 0: return
        x = (x-1) & n

def hf_switch(x: int) -> list[int]:
    if x and not x & (x-1): return [x.bit_length()-1]
    return list(submasks(x))

def hf_hull(a: int, subset_seed: bool = False) -> set[int]:
    todo = list(submasks(a)) if subset_seed else [a]
    expanded: set[int] = set(); reached: set[int] = set()
    while todo:
        x = todo.pop()
        if x in expanded: continue
        expanded.add(x)
        for y in hf_switch(x):
            reached.add(y)
            if y not in expanded: todo.append(y)
    return reached

def hereditary_finite() -> dict:
    local_outputs = transport = members_checked = root_omissions = 0
    for a in range(4096):
        bound = a.bit_length()-1 if a and not a & (a-1) else a
        for y in hf_switch(a):
            require(y & ~bound == 0, ('local',a,y,bound)); local_outputs += 1
        h = hf_hull(a); hmask = sum(1 << x for x in h)
        require(a & ~hmask == 0, ('root members',a))
        if a not in h: root_omissions += 1
        for x in h:
            require(x & ~hmask == 0, ('transitive',a,x)); members_checked += 1
        for y in set(submasks(a)) | set(bits(a)):
            require(y & ~hmask == 0, ('transport',a,y)); transport += 1
        h2 = hf_hull(a, True); m2 = sum(1 << x for x in h2)
        require(a & ~m2 == 0 and all(x & ~m2 == 0 for x in h2), ('subsetseed',a))
    return {'roots':4096, 'seed_modes':2, 'local_output_bounds':local_outputs,
            'point_hull_members':members_checked, 'mixed_to_subset_transports':transport,
            'point_hulls_omitting_the_root':root_omissions,
            'note':'HF roots are finite regression inputs, not models of the infinite axiom schema.'}

def finite_local_lemma() -> dict:
    graphs = candidate_pairs = valid = nonextensional = self_membership = transport = 0
    for n in range(1,5):
        mask = (1<<n)-1
        for graph in range(1 << (n*n)):
            ext = [(graph >> (n*x)) & mask for x in range(n)]; graphs += 1
            single_covered = 0
            for row in ext:
                if row and not row & (row-1): single_covered |= row
            switch = []
            for row in ext:
                switch.append(row if row and not row & (row-1) else
                              sum(1<<y for y in range(n) if ext[y] & ~row == 0))
            for a in range(n):
                for c in range(n):
                    cmem = ext[c]
                    for subset_seed in [False, True]:
                        candidate_pairs += 1
                        seeds = sum(1<<x for x in range(n) if ext[x] & ~ext[a] == 0) if subset_seed else 1<<a
                        active = seeds | cmem
                        if any(switch[x] & ~cmem for x in bits(active)): continue
                        # Only singletons needed by a nonsingleton active input are assumed.
                        need = 0
                        for x in bits(active):
                            if ext[x].bit_count() != 1: need |= ext[x]
                        if need & ~single_covered: continue
                        valid += 1
                        nonextensional += len(set(ext)) < n
                        self_membership += any(ext[x] & (1<<x) for x in range(n))
                        require(ext[a] & ~cmem == 0, (n,graph,a,c,'seed'))
                        require(all(ext[x] & ~cmem == 0 for x in bits(cmem)), (n,graph,a,c,'trans'))
                        for b in range(n):
                            if ext[b] & ~cmem: continue
                            for y in range(n):
                                if ext[b] & (1<<y) or ext[y] & ~ext[b] == 0:
                                    require(ext[y] & ~cmem == 0, 'bound transport'); transport += 1
    return {'membership_graphs':graphs, 'root_witness_seedmode_checks':candidate_pairs,
            'cases_satisfying_local_hypotheses':valid,
            'such_cases_with_duplicate_member_profiles':nonextensional,
            'such_cases_with_self_membership':self_membership, 'bound_transport_checks':transport,
            'note':'This tests the local lemma, not whole finite models of the calibrated theory.'}

def direct_schema(ext: list[int], rel: list[int], seed: str, mixed: bool,
                  purity: bool = True, initial: bool = True, membership_only: bool = False) -> bool:
    n = len(ext)
    def bounded(y,b):
        sub = ext[y] & ~ext[b] == 0
        mem = bool(ext[b] & (1<<y))
        return mem if membership_only else (sub or mem) if mixed else sub
    local = all(any(all(not rel[x] & (1<<y) or bounded(y,b) for y in range(n)) for b in range(n)) for x in range(n))
    if not local: return True
    for a in range(n):
        works = False
        for c in range(n):
            def active(x):
                seeded = (x == a) if seed == 'point' else ext[x] & ~ext[a] == 0
                return (initial and seeded) or bool(ext[c] & (1<<x))
            closed = all(not (active(x) and rel[x] & (1<<y)) or ext[c] & (1<<y) for x in range(n) for y in range(n))
            support = not purity or all(not ext[c] & (1<<y) or any(rel[x] & (1<<y) for x in range(n)) for y in range(n))
            if closed and support: works = True; break
        if not works: return False
    return True

def formula_semantics() -> dict:
    rng = random.Random(123456); checks = 0
    templates = {(s,m,c):closure(Hole(0,1),s,m,False,c) for s in ('point','subset') for m in (False,True) for c in (False,True)}
    cases = []
    for n in (1,2):
        for g in range(1 << (n*n)):
            ext = [(g>>(n*x)) & ((1<<n)-1) for x in range(n)]
            for r in range(1 << (n*n)):
                rel = [(r>>(n*x)) & ((1<<n)-1) for x in range(n)]
                cases.append((ext,rel))
    cases += [([rng.randrange(8) for _ in range(3)], [rng.randrange(8) for _ in range(3)]) for _ in range(2000)]
    for ext,rel in cases:
        for (s,m,c), f in templates.items():
            require(evaluate(f,ext,{},rel) == direct_schema(ext,rel,s,m), (ext,rel,s,m,c)); checks += 1
    deletion = {}
    for s in ('point','subset'):
        deletion['without_purity_'+s] = all(direct_schema([1],[r],s,False,purity=False) for r in (0,1))
        deletion['without_seed_'+s] = all(direct_schema([0],[r],s,False,initial=False) for r in (0,1))
        deletion['membership_only_'+s] = all(direct_schema([0],[r],s,False,membership_only=True) for r in (0,1))
    require(all(deletion.values()), deletion)
    return {'schema_semantics_comparisons':checks, 'one_object_deletion_models':deletion}

def main():
    data = {'status':'PASS', 'scope':'Executable finite regressions; not formal proof certificates.',
            'finite_local_lemma':finite_local_lemma(), 'hereditary_finite':hereditary_finite(),
            'formula_semantics':formula_semantics()}
    path = Path(__file__).resolve().parents[1]/'results'/'experiments.json'
    path.write_text(json.dumps(data,indent=2)+'\n'); print(json.dumps(data,indent=2))

if __name__ == '__main__': main()
