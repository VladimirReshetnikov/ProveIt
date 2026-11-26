"""Round the local exchange bound and rough-prime tail outwards using integers."""
from math import isqrt

GAIN_NUM = 23
GAIN_DEN = 10000
Y = 6841
END = 2000000
UNIT = 10**18

def primes(limit):
    live = bytearray([1]) * (limit + 1)
    live[:2] = bytes(2)
    for d in range(2, isqrt(limit)+1):
        if live[d]:
            live[d*d::d] = bytes((limit-d*d)//d+1)
    return (p for p in range(limit+1) if live[p])

def main():
    product_lo = UNIT
    tax_hi = (UNIT+END-1)//END
    for p in primes(END):
        if p <= Y:
            product_lo = product_lo*(p-1)//p
        else:
            tax_hi += (UNIT+p*p-1)//(p*p)
    gap_lo = product_lo*GAIN_NUM//GAIN_DEN-tax_hi
    print("lower bound on", UNIT, "times the natural-density separation:", gap_lo)
    assert gap_lo > 1306*UNIT//10_000_000
if __name__ == "__main__":
    main()
