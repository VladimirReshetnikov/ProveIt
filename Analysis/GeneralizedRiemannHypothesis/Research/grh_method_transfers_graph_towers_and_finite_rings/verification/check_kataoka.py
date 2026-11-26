#!/usr/bin/env python3
"""Check Kataoka, arXiv:2606.03579v1, Tables 6 and 7, by exact cyclotomic arithmetic."""
from check_graphs import cofactor, directions, mod_symbol_order, projections, shell, vp

X, Y = (1,0), (0,1)
STEPS = {
    0: ((3,2),X,Y),
    1: ((2,2),X,Y),
    2: (X,Y,Y),
    3: ((1,1),X,Y),
    4: ((2,0),X,X,Y,Y),
    5: ((2,2),(2,1),(1,2),X,Y),
    6: ((3,0),X,Y,Y),
    7: ((3,3),(3,2),(2,3),(2,1),(1,2),(1,1)),
    8: ((4,0),X,X,Y,Y),
}
# T_n = lambda*n*2^n + half_b*2^(n-1) + c*n + d for n>=start.
LAWS = {
    0: (18,-2,-3,3), 1: (15,-4,-7,3), 2: (0,2,1,2),
    3: (18,-8,-9,1), 4: (-8,6,8,2), 5: (10,-16,22,3),
    6: (-20,14,14,3), 7: (8,-20,14,3), 8: (-32,14,6,2),
}


def main():
    for index,steps in STEPS.items():
        b,c,d,start = LAWS[index]
        values = []
        total = 0
        for n in range(1,10):
            total += shell(2,n,steps)-2
            if n >= start:
                assert total == (index*n*2 + b)*2**(n-1)+c*n+d
            if n <= 3:
                assert total == vp(cofactor(2,n,steps),2)
            values.append(total)
        print(f"lambda={index}, n=1..9: {values}")
    print("lambda=0 mod-8 orders:",
          [(u,mod_symbol_order(2,8,projections(u,STEPS[0]))) for u in directions(2,3,2)])
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
