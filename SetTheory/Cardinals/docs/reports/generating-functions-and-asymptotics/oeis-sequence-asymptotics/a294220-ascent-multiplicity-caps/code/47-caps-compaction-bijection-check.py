#!/usr/bin/env python3
"""Test the explicit binary-block involution against labeled raw suffixes."""
from itertools import product
import json

def suffixes(b, initial, last, n, upper=None):
    if upper is None:
        upper = len(initial)-1
        initial = dict(enumerate(initial))
    if n == 0:
        yield ()
        return
    for x in tuple(initial):
        child = dict(initial)
        child[x] -= 1
        if child[x] == 0:
            del child[x]
        asc = x > last
        if asc:
            child[upper+1] = b
        for tail in suffixes(b,child,x,n-1,upper+asc):
            yield (x,)+tail

def phi(word,x,y):
    ans = list(word)
    i = 0
    while i < len(word):
        if word[i] not in (x,y):
            i += 1
            continue
        j = i+1
        while j < len(word) and word[j] in (x,y):
            j += 1
        ans[i:j] = [y if c==x else x for c in reversed(word[i:j])]
        i = j
    return tuple(ans)

def valid(b,initial,last,word):
    remaining = dict(enumerate(initial))
    upper = len(initial)-1
    for x in word:
        if x not in remaining:
            return False
        remaining[x] -= 1
        if remaining[x] == 0:
            del remaining[x]
        if x > last:
            upper += 1
            remaining[upper] = b
        last = x
    return True

def ascents(last,word):
    return sum(a<c for a,c in zip((last,)+word,word))

if __name__ == '__main__':
    result = {}
    for b in (3,4):
        checked = 0
        for m in (2,3):
            for budgets in product(range(1,b+1),repeat=m):
                for k in range(2,m+1):
                    for r in range(k-1):
                        if budgets[r] == budgets[r+1]:
                            continue
                        swapped = list(budgets)
                        swapped[r],swapped[r+1] = swapped[r+1],swapped[r]
                        for word in suffixes(b,budgets,k-1,5):
                            mapped = phi(word,r,r+1)
                            assert phi(mapped,r,r+1)==word
                            assert ascents(k-1,mapped)==ascents(k-1,word)
                            assert valid(b,swapped,k-1,mapped), (b,budgets,k,r,word,mapped)
                            checked += 1
        result[b] = {'individual_suffix_involution_checks_n5_m_le_3': checked}
    print(json.dumps(result,indent=2))
