"""Finite fixtures for simultaneous orientation and power authentication.

These are falsification checks, not an unbounded theorem prover.
"""
from fractions import Fraction
import json


def require(condition, description):
    if not condition:
        raise ValueError(description)


def pell(a, k):
    x, y = 1, 0
    for _ in range(abs(k)):
        x, y = a*x+(a*a-1)*y, x+a*y
    return x, -y if k < 0 else y


def pool(a, pairs, blocks):
    """Pair entries: (actual_signed_index, requested_index, sign).

    Each request is (output, pair_index). Nonzero-base exactness uses
    the requested index; before authentication these need not coincide.
    """
    raw = [(e*x,e*y) for nu,_,e in pairs for x,y in [pell(a,nu)]]
    omega = sum((x-1)**2+(y-k)**2
                for (x,y),(_,k,_) in zip(raw,pairs))
    small_o = sum((e-1)**2+(e*nu-k)**2 for nu,k,e in pairs)
    require((omega-small_o) % (a-1) == 0, "raw orientation residue")
    value = Fraction(omega,a-1)
    for n,requests in blocks:
        t = 2*a*n-n*n-1
        h = s = delta_square = y_square = 0
        for m,i in requests:
            x,y=raw[i]
            h += y*(m-x)
            s += (m-x+a*y)**2-y*y
            delta_square += (m-x+(a-n)*y)**2
            y_square += y*y
        e=s-2*n*h
        require(e-t*y_square==delta_square,"raw norm error identity")
        value += Fraction(n*e,t)
    return value


def main():
    w=258
    a0=w**w+1
    valid=bad_sign=bad_index=bad_output=0
    for a in (a0,-a0):
        for bases in ([0,1,-1,2,-3],[3,-2,0,-1,1],[0,0,0,0,0]):
            pairs=[];blocks=[]
            for n in bases:
                req=[]
                for k in ((-1,0,1) if abs(n)==1 else (0,1,2)):
                    idx=len(pairs);pairs.append((k,k,1))
                    m=(4 if n==0 else ((1 if n==1 or k%2==0 else -1)
                       if k<0 else n**k))
                    req.append((m,idx))
                blocks.append((n,req))
            # The theorem permits at most15 principal pairs and17 requests.
            require(len(pairs)==15,"pair count")
            require(pool(a,pairs,blocks).denominator==1,"valid profile")
            valid+=1
            for i,(nu,k,eps) in enumerate(pairs):
                wrong=list(pairs);wrong[i]=(nu,k,-eps)
                require(pool(a,wrong,blocks).denominator!=1,"sign error escaped")
                bad_sign+=1
                wrong=list(pairs);wrong[i]=(nu+1,k,eps)
                require(pool(a,wrong,blocks).denominator!=1,"index error escaped")
                bad_index+=1
            for j,(n,requests) in enumerate(blocks):
                if n==0:
                    continue
                for r,(m,i) in enumerate(requests):
                    wrong=[(nn,list(rr)) for nn,rr in blocks]
                    wrong[j][1][r]=(m+1,i)
                    require(pool(a,pairs,wrong).denominator!=1,"output error escaped")
                    bad_output+=1
    print(json.dumps({"status":"PASS","valid_profiles":valid,
          "wrong_raw_coordinate_signs_rejected":bad_sign,
          "wrong_classified_indices_rejected":bad_index,
          "wrong_nonzero_base_outputs_rejected":bad_output,
          "W":w,"A_description":"both signs of 258^258+1",
          "scope":"Finite fixtures only; unbounded proof supplied separately."},
          indent=2,sort_keys=True))


if __name__=="__main__":
    main()
