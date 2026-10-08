from itertools import product
from collections import Counter
from whitehead_exposure.algebra import cyclic_reduce, whitehead_image, word_graph, cut_capacity

def all_moves(alive):
    V = sorted([-g for g in alive]+list(alive))
    for a in V:
        free = [v for v in V if v not in (a,-a)]
        for mask in range(1 << len(free)):
            yield a, {a} | {v for i,v in enumerate(free) if mask>>i&1}

def literal_oracle(words, alive, objective='allocation'):
    best = None
    for a,S in all_moves(alive):
        image = [cyclic_reduce(y for x in w for y in whitehead_image(x,a,S)) for w in words]
        total = sum(map(len,image))
        count = sum(abs(x)==abs(a) for w in image for x in w)
        for j,w in enumerate(image):
            if sum(abs(x)==abs(a) for x in w) != 1:
                continue
            U = total-len(w)+(count-1)*(len(w)-2)
            delta = total-sum(map(len,words))
            score = (U,delta) if objective=='allocation' else (delta,U)
            if best is None or score<best:
                best=score
    return best

def random_word(rng, rank, length):
    return cyclic_reduce(rng.choice([-1,1])*rng.randint(1,rank) for _ in range(length))

def barrier(m):
    from whitehead_exposure.algebra import inverse
    u=(1,1,2,1,2); t=(1,-2)*3
    v=cyclic_reduce(u+t+inverse(u)+inverse(t))
    return [u,v*m]
