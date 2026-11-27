"""Recover low positive zeta ordinates from Cauchy samples of xi at its center.

Requires mpmath 1.3.0. The quadrature is high-precision numerical evidence.
No zero ordinates enter the estimator. zetazero is used only for comparison.
"""
import argparse
from math import comb
import mpmath as mp


def xi(s):
    return s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s) / 2


def moments(max_order, nodes, scale):
    # The entire function of z below equals product(1 + scale*z/gamma**2).
    # The samples at conjugate nodes are conjugates, so half a circle suffices.
    assert nodes % 2 == 0 and nodes > max_order
    center = mp.mpf("0.5")
    base = xi(center)
    angles = [mp.mpf(2)*mp.pi*j/nodes for j in range(nodes//2+1)]
    samples = [xi(center + mp.sqrt(scale)*mp.expj(a/2))/base for a in angles]
    weights = [1]+[2]*(len(angles)-2)+[1]
    elementary = [mp.mpf(1)]
    power = [mp.mpf(0)]
    for j in range(1, max_order+1):
        coefficient = mp.fsum(w*mp.re(v*mp.expj(-j*a))
                              for w,v,a in zip(weights,samples,angles))/nodes
        elementary.append(coefficient)
        correction = mp.fsum((-1)**(i-1)*power[i]*elementary[j-i] for i in range(1,j))
        power.append((-1)**(j-1)*(j*coefficient-correction))
    return power


def roots_for_block(power, k, max_degree):
    rank = int(mp.floor(power[k]**2/power[2*k]))
    center = power[k]/rank
    elementary = [mp.mpf(1)]
    roots = [None]
    for d in range(1,max_degree+1):
        elementary.append(mp.fsum((-1)**(j-1)*power[j*k]*elementary[d-j]
                                  for j in range(1,d+1))/d)
        coefficients = [(-1)**j*comb(rank+j-1,j)*elementary[d-j] for j in range(d,-1,-1)]
        fn = lambda t: mp.polyval(coefficients,t)
        candidate = mp.findroot(fn, (center, center*mp.mpf("1.0001")), verify=True)
        # Check the chosen root is nearest to the prescribed center. A
        # symmetric interval and a derivative Taylor bound suffice here.
        derivative = [coef*(d-i) for i,coef in enumerate(coefficients[:-1])]
        radius = max(2*abs(center-candidate), abs(center)*mp.mpf("1e-25"))
        shifted = [mp.fsum(comb(j,i)*v*center**(j-i)
                           for j,v in enumerate(reversed(derivative)) if j>=i)
                   for i in range(d)]
        assert abs(shifted[0]) > mp.fsum(abs(shifted[j])*radius**j for j in range(1,d))
        assert fn(center-radius)*fn(center+radius)<0
        roots.append(candidate)
    return rank, roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits",type=int,default=150)
    parser.add_argument("--nodes",type=int,default=192)
    args = parser.parse_args()
    mp.mp.dps=args.digits
    scale = mp.mpf(200)
    orders = (4,8,16,24,32)
    power = moments(4*(max(orders)+1),args.nodes,scale)
    print("Scaled positive-ordinate moments of xi from Cauchy sampling")
    print("decimal digits =",args.digits,"   nodes =",args.nodes)
    print("k   r    order-3 first ordinate     second via gaps     third via gaps      fourth via gaps")
    for k in orders:
        rank, roots = roots_for_block(power,k,4)
        one_over_k = mp.mpf(1)/k
        leading = (power[k]/rank)**one_over_k
        differences = [leading]+[abs(roots[d]-roots[d+1])**one_over_k for d in range(1,4)]
        recovered = [mp.sqrt(scale/(leading*differences[d]/differences[d-1])) for d in range(1,4)]
        first = mp.sqrt(scale/roots[3]**one_over_k)
        print(k,rank,*[mp.nstr(z,17) for z in [first]+recovered],sep="   ")
    print("Consecutive-stride estimates, using k and k+1")
    print("k    second ordinate     third ordinate      fourth ordinate")
    for k in orders:
        _, left = roots_for_block(power,k,4)
        _, right = roots_for_block(power,k+1,4)
        ratios = [power[k+1]/power[k]]
        for d in range(1,4):
            ratios.append(abs((right[d+1]-right[d])/(left[d+1]-left[d])))
        estimates = [mp.sqrt(scale*ratios[d-1]/(ratios[0]*ratios[d]))
                     for d in range(1,4)]
        print(k,*[mp.nstr(z,17) for z in estimates],sep="   ")
    print("External comparison, mpmath.zetazero 1 through 4")
    print("   ".join(mp.nstr(mp.im(mp.zetazero(i)),17) for i in range(1,5)))


if __name__ == "__main__":
    main()
