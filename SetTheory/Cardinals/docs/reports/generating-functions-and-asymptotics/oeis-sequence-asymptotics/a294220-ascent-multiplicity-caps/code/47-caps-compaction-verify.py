#!/usr/bin/env python3
"""Independent bounded-ascent-sequence and compacted-state checks."""
from functools import lru_cache
from itertools import product
import json

@lru_cache(None)
def raw_budget_count(b, budgets, k, n):
    if n == 0:
        return 1
    ans = 0
    for i, r in enumerate(budgets):
        asc = int(i >= k)
        child = list(budgets)
        if r == 1:
            del child[i]
            nk = i
        else:
            child[i] -= 1
            nk = i + 1
        if asc:
            child.append(b)
        ans += raw_budget_count(b, tuple(child), nk, n-1)
    return ans

@lru_cache(None)
def grouped_count(b, counts, k, n):
    # counts[r-1] = number of labels with remaining budget r, 1 <= r <= b
    if n == 0:
        return 1
    ans = 0
    left = 0
    for r, num in enumerate(counts, 1):
        for i in range(left, left + num):
            asc = int(i >= k)
            child = list(counts)
            child[r-1] -= 1
            if r > 1:
                child[r-2] += 1
            child[b-1] += asc
            nk = i if r == 1 else i+1
            ans += grouped_count(b, tuple(child), nk, n-1)
        left += num
    return ans


def direct_ascent_counts(b, nmax):
    # Enumerate actual words, independently of rank/budget deletion or compaction.
    counts = [1] + [0]*nmax
    def walk(word, usages, asc):
        n = len(word)
        counts[n] += 1
        if n == nmax:
            return
        for x in range(asc+2):
            if usages.get(x,0) >= b:
                continue
            usages[x] = usages.get(x,0)+1
            walk(word+(x,), usages, asc + int(x > word[-1]))
            usages[x] -= 1
    if nmax:
        walk((0,), {0:1}, 0)
    return counts


def check_totals(b, nmax):
    direct = direct_ascent_counts(b, nmax)
    initial = tuple([int(r == b-1) + int(r == b) for r in range(1,b+1)])
    grouped = [1] + [grouped_count(b, initial, 1, n-1) for n in range(1,nmax+1)]
    raw = [1] + [raw_budget_count(b,(b-1,b),1,n-1) for n in range(1,nmax+1)]
    assert direct == grouped == raw, (b,direct,grouped,raw)
    return direct


def check_adjacent_swaps(b, mmax, nmax):
    checks = 0
    for m in range(2,mmax+1):
        for budgets in product(range(1,b+1), repeat=m):
            for k in range(2,m+1):
                for j in range(k-1):
                    if budgets[j] == budgets[j+1]:
                        continue
                    swapped = list(budgets)
                    swapped[j], swapped[j+1] = swapped[j+1], swapped[j]
                    swapped = tuple(swapped)
                    for n in range(1,nmax+1):
                        left = raw_budget_count(b,budgets,k,n)
                        right = raw_budget_count(b,swapped,k,n)
                        assert left == right, (b,budgets,k,j,n,left,right)
                        checks += 1
    return checks


def check_grouped_states(b,mmax,nmax):
    checks = 0
    for m in range(1,mmax+1):
        for budgets in product(range(1,b+1),repeat=m):
            if tuple(sorted(budgets)) != budgets:
                continue
            counts = tuple(budgets.count(r) for r in range(1,b+1))
            for k in range(m+1):
                for n in range(nmax+1):
                    left = raw_budget_count(b,budgets,k,n)
                    right = grouped_count(b,counts,k,n)
                    assert left == right, (b,budgets,k,n,left,right)
                    checks += 1
    return checks

if __name__ == '__main__':
    results = {}
    for b in (3,4):
        results[b] = {
            'actual_word_totals_through_n9': check_totals(b,9),
            'adjacent_swap_checks_m_le_4_suffix_le_5': check_adjacent_swaps(b,4,5),
            'grouped_state_checks_m_le_5_suffix_le_5': check_grouped_states(b,5,5),
        }
        raw_budget_count.cache_clear()
        grouped_count.cache_clear()
    print(json.dumps(results,indent=2))
