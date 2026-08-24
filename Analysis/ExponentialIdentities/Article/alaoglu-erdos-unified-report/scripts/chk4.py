import math
M,A=5,11
lM,lA=math.log(M),math.log(A)
print("theta grid: cells with 7/12 < (n+i)lnM/((m+j)lnA) < 1, and whether K<=N/2")
bad=0; tot=0
for L in range(1,60):          # L = n+i
    for T in range(1,60):      # T = m+j
        th=L*lM/(T*lA)
        if 7/12 < th < 1:
            tot+=1
            K=M**L; N=A**T
            if K> N//2: bad+=1; print("   script-admissible but K>N/2:  M^%d=%d  A^%d=%d  theta=%.4f"%(L,K,T,N,th))
print("script-admissible (L,T) pairs:",tot," of which violate K<=N/2:",bad)

# H4 feasibility in the M=5,A=11 laboratory: A > 16 Z (m+j*) ln A
print()
print("H4 at A=11 with the SMALLEST possible Z=1, m+j*=1:  16*1*1*ln11 =",16*math.log(11),"  vs A=11 -> H4",
      "holds" if 11>16*math.log(11) else "FAILS")
for beta in (14,20,30):
    A3=3**beta; print(f"beta={beta}: A={A3:.4g}, A/(16 lnA) = {A3/(16*math.log(A3)):.4g}")
# linear-width family: Z ~ 0.585 L, m+j* ~ 0.631 L  (L = n+i top level)
for beta in (14,20,30):
    A3=3**beta; cap=A3/(16*math.log(A3))
    import math as mm
    # solve 0.585*L * 0.631*L < cap
    L=(cap/(0.585*0.631))**0.5
    print(f"beta={beta}: H4 caps the critical-width family at top level L < {L:.1f}")
