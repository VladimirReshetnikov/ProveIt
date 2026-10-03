from functools import lru_cache
@lru_cache(None)
def endpoints(rows):
    s={0}
    for row in rows:
        s={v|(1<<i) for v in s for i in range(4) if row>>i&1 and not v>>i&1}
    return s
@lru_cache(None)
def norm(rows):
    return sum(15^s for s in endpoints(rows))
@lru_cache(None)
def basis(rows):
    return 15 in endpoints(rows)
