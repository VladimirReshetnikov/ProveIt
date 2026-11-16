"""Finite bounded search reference; NOT an iPRA proof checker."""
def search(n, predicate):
    assert n >= 0
    for i in range(n):
        if predicate(i):
            return i, True
    return n, False

def universal(n, predicate):
    return all(predicate(i) for i in range(n))

def existential(n, predicate):
    return any(predicate(i) for i in range(n))

def staged(n, first, bound, second):
    i, success = search(n, first)
    if not success:
        return n, 0, False
    j, success2 = search(bound(i), lambda k: second(i, k))
    return i, j, success2

def regression():
    for n in range(32):
        for k in range(45):
            pred = lambda i: i*i == k
            w, ok = search(n, pred)
            assert ok == existential(n, pred)
            assert ok == (w < n)
            assert universal(n, lambda i: not pred(i)) == (not ok)
            if ok:
                assert pred(w) and all(not pred(i) for i in range(w))
            else:
                assert w == n
    for n in range(20):
        for k in range(n):
            assert staged(n, lambda i: i == k, lambda i: i+1,
                          lambda i,j: j==i) == (k,k,True)
    assert staged(0, lambda i: True, lambda i: 3,lambda i,j: True) == (0,0,False)
if __name__ == '__main__':
    regression()
    print('Finite reflection regressions passed')
