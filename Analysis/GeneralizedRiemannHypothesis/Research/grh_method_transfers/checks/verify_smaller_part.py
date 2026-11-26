"""Verify the transfer E_{m,n} -> E_{m+1,n} for all n >= m."""
from argparse import ArgumentParser
from verify_ehrhart import differences, normalized_coords
from verify_interlacing import multiply, positive_on_halfline


def transition_in_width(r, n):
    a,b=normalized_coords(r,n)
    c,d=normalized_coords(r+1,n)
    output = [u-v for u,v in zip(multiply(a,d),multiply(b,c))]
    assert all(v==0 for v in output[1::2])
    return output[::2]


def certify_width(m):
    r=m-1
    # Confirm degree bounds in the larger width at the chosen base n=m.
    # This includes width 33, which does not need a Bezoutian test.
    k=r+1
    sample=[normalized_coords(k,m+t) for t in range(7*k+1)]
    for side,bound in enumerate((k,k+1)):
        for seq in zip(*(pair[side] for pair in sample)):
            for _ in range(bound+1):
                seq=differences(seq)
            assert not any(seq)
    # Degrees in n for A_r,B_{r+1} are <=r,r+2 and for B_r,A_{r+1}
    # are <=r+1,r+1, so this sample determines the whole polynomial.
    rows=[transition_in_width(r,m+t) for t in range(2*r+3)]
    assert positive_on_halfline(rows[0])
    nonzero=0
    while rows:
        if any(rows[0]):
            assert positive_on_halfline(rows[0]), (m,nonzero)
            nonzero+=1
        rows=[[v-u for u,v in zip(a,b)] for a,b in zip(rows,rows[1:])]
    return nonzero


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to enable certificate assertions')
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('first',type=int,nargs='?',default=6)
    parser.add_argument('last',type=int,nargs='?',default=None)
    args=parser.parse_args()
    for m in range(args.first, (args.last or args.first)+1):
        print(f'm={m}  positive width-transfer Newton polynomials={certify_width(m)}',flush=True)
