#!/usr/bin/env python3
"""Own exact-arithmetic regression tests; no dependencies and no SAT claim.

Checks explicit parameter inequalities, a rational C<85 certificate, the
conditional-expectation matching packing on small multigraphs, and taper sums.
"""
from fractions import Fraction as F
from math import ceil, log2, log, pi, sqrt
from random import Random
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent

def require(condition, message="Exact verification failed"):
    if not condition:
        raise RuntimeError(message)

def greedy_colors(edges):
    classes = []
    occupied = []
    for edge in edges:
        for j, used in enumerate(occupied):
            if not any(v in used for v in edge):
                classes[j].append(edge)
                used.update(edge)
                break
        else:
            classes.append([edge])
            occupied.append(set(edge))
    return classes

def potential(classes, q, lam, labels):
    d = q*q
    z = F(lam+1, lam)
    result = F(0)
    for es in classes:
        threshold = ceil(F(lam+1,lam)*F(len(es),d)+10*lam*lam)
        for a in range(q):
            for b in range(q):
                product = F(1)
                for x,y in es:
                    px = F(int(labels[x] == a)) if x in labels else F(1,q)
                    py = F(int(labels[y] == b)) if y in labels else F(1,q)
                    product *= 1 + px*py/F(lam)
                result += product / z**threshold
    return result

def packing_case(edges,q,lam):
    classes = greedy_colors(edges)
    vertices = sorted({v for e in edges for v in e})
    degrees = {v: sum(v in e for e in edges) for v in vertices}
    delta = max(degrees.values())
    require(len(classes) <= 2*delta-1)
    require(all(len({v for e in es for v in e}) == 2*len(es) for es in classes))
    labels = {}
    initial = potential(classes,q,lam,labels)
    require(initial < 1)
    conditional_checks = 0
    for v in vertices:
        old = potential(classes,q,lam,labels)
        options = []
        for a in range(q):
            labels[v] = a
            options.append(potential(classes,q,lam,labels))
        del labels[v]
        require(sum(options,F(0))/q == old)
        labels[v] = min(range(q),key=lambda a: options[a])
        require(potential(classes,q,lam,labels) <= old)
        conditional_checks += 1
    final = potential(classes,q,lam,labels)
    require(final <= initial)
    for es in classes:
        threshold = ceil(F(lam+1,lam)*F(len(es),q*q)+10*lam*lam)
        for a in range(q):
            for b in range(q):
                load = sum(labels[x]==a and labels[y]==b for x,y in es)
                require(load < threshold)
    loads = [sum(labels[x]==a and labels[y]==b for x,y in edges)
             for a in range(q) for b in range(q)]
    require(max(loads) < F(lam+1,lam)*F(len(edges),q*q)+20*delta*lam*lam)
    return conditional_checks

def main():
    eps0=F(10,1043)
    eps1=F(1,236)
    A=eps0+eps1*F(5,3)
    require(37**200 < 2**1043)
    require(F(9,10)+6*A < 1)
    require(7*A < 1)
    # Cruder rational inequalities certify C<85 without floating-point reliance.
    sx, sy, sz = F(8226,1000),F(11734,1000),F(1582,1000)
    require(sx*sx>F(12516,185) and sy*sy>F(413,3) and sz*sz>F(5,2))
    # Classical pi<22/7 and ln2>69/100. The latter also follows from
    # ln2 = 2 sum_{j>=0} (1/3)^(2j+1)/(2j+1), taking j=0,1,2.
    ln2_lower = 2*sum((F(1,3)**(2*j+1)/F(2*j+1) for j in range(3)),F(0))
    require(ln2_lower > F(69,100))
    rational_upper = 2*F(22,7)/F(69,100)*(sx+F(2,37)*sy/(1-sz/4))
    require(rational_upper < 85)
    K=lambda r:2*pi*sqrt(F(2,3)*(1-F(1,r)))/log(2)
    coeff=K(37)/sqrt(eps0)+F(2,37)*K(8)/(sqrt(eps1)*(1-sqrt(F(5,2))/4))
    taper_checks=0
    for a in range(2,18):
        L=2**a
        for u in range(1,a+1):
            W=sum((L//2**i)*(u-i) for i in range(u))
            require(W == F(L)*(2*u-2+F(2,2**u)))
            for M in [u,3*u,100,1000]:
                if M<u: continue
                degree=M*(2*L-1)
                h=ceil(F(degree+1,W))
                require(h*W>degree and (h-1)*W<=degree)
                qs=[h*(u-i) if i<u else 0 for i in range(a+1)]
                for i in range(u):
                    B=sum(j*2**(a-i-j)*(qs[i]-qs[i+j]) for j in range(1,a-i+1))
                    require(0 < B <= 6*h*2**(a-i))
                taper_checks+=1
    rng=Random(20261027)
    potential_cases=0; conditional_checks=0
    # Includes multiple parallel edges and nonuniform matching sizes.
    graphs=[[(0,10)]*8,[(0,10),(0,10),(0,11),(1,10),(2,12)],
            [(i,10+j) for i in range(3) for j in range(3)]]
    graphs += [[(rng.randrange(4),10+rng.randrange(4)) for _ in range(rng.randrange(1,13))]
               for _ in range(18)]
    for edges in graphs:
        for q in [2,3]:
            conditional_checks += packing_case(edges,q,2)
            potential_cases+=1
    output={
        'status':'passed', 'scope':'finite exact regression checks, not end-to-end SAT or asymptotic proof',
        'coefficient_decimal':float(coeff), 'coefficient_rational_upper':str(rational_upper),
        'coefficient_rational_upper_decimal':float(rational_upper),
        'coefficient_less_than_85':True, 'checks_active_under_python_optimization':True,
        'root_packing_integer_inequality':'37**200 < 2**1043',
        'root_packing_exponent':.9+2*float(eps0)*log2(37),
        'tail_packet_exponent_A':str(A),
        'tail_packing_exponent_exact':str(F(9,10)+6*A),
        'tail_packing_exponent_decimal':float(F(9,10)+6*A),
        'tail_u_power':1-log(2.5)/log(4),
        'taper_cases':taper_checks,'multigraph_packing_cases':potential_cases,
        'conditional_expectation_exact_mean_checks':conditional_checks,
        'input_code_executed':'Only this newly authored file; no supplied repository code executed.'
    }
    (OUT/'combined_verification.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':main()
