"""A triangle with unequal edge lengths, exact finite observations."""
from fractions import Fraction as F
from sparse import Ask, aggregates, carry_error, leaves, run


def affine_tree(start, end, m):
    def build(depth, prefix):
        if depth == m:
            t = F(2 * prefix + 1, 1 << (m+1))
            return start + (end-start)*t
        return Ask(depth, build(depth+1,2*prefix), build(depth+1,2*prefix+1))
    return build(0,0)


def check():
    heights = [0,1,-1]
    lengths = [1,2,3]
    for m in range(7):
        eps = F(1,1<<m)
        trees = [affine_tree(v, heights[(i+1)%3], m) for i,v in enumerate(heights)]
        means = []
        for i,t in enumerate(trees):
            rows = leaves(t)
            assert carry_error(rows) <= 2*eps
            assert abs(run(t, lambda _: 1) - run(trees[(i+1)%3],lambda _: 0)) <= 2*eps
            means.append(aggregates(rows)[1])
        assert sum(a*b for a,b in zip(lengths,means))/sum(lengths) == F(-1,6)
    print("Metric triangle: edge and vertex tests passed at 7 levels; "
          "normalized arclength integral = -1/6.")


if __name__ == "__main__":
    check()
