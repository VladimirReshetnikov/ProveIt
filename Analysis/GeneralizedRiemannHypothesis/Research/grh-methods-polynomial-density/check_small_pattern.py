"""Verify a finite replacement used with M = 3**8.

The masks below encode two ordinary AP-free sets listed by J. Wroblewski
in https://www.math.uni.wroc.pl/~jwr/non-ave/DATABASE.TXT . The entries
are the a(106) <= 795 and a(151) <= 1241 lists. Each is translated to
start at zero, and bit n represents membership of n. No input files,
external dependencies, network requests, or random choices are needed.
"""

U_MASK = (
    "53280a6500000029940532880001000000000400008098283305000000cc141983000020000000"
    "00800010000000000000000000000000000000000000000000000b1a0163400000058d00b1a000"
    "80001000000000400008198283304000020cc141983"
)
V_MASK = (
    "10340861001680c300000030c05a0021840b020000000820002008802000208000000206810c20"
    "02d01860000006180b400430816000000000000000000000000000000000000000000000000000"
    "00000000000000000008000000208000802200800082000000081a0430800b406180000018602d"
    "0010c20581000000041000100440100010400000010340861001680c300000030c05a0021840b"
)


def decode(mask):
    number = int(mask, 16)
    return {i for i in range(number.bit_length()) if (number >> i) & 1}


def check_no_progression(values):
    for left in values:
        for middle in values:
            if left < middle and 2 * middle - left in values:
                raise ValueError(f"Progression: {left}, {middle}, {2*middle-left}")


def main():
    u, v = decode(U_MASK), decode(V_MASK)
    assert (len(u), min(u), max(u)) == (106, 0, 794)
    assert (len(v), min(v), max(v)) == (151, 0, 1240)
    check_no_progression(u)
    check_no_progression(v)
    union = u | {2035 + x for x in v}
    check_no_progression(union)
    assert len(union) == 257 and max(union) == 3275
    assert len(union) > 2**8 and 2 * max(union) < 3**8
    assert 257 * 513**2 - 256 * 514**2 == 257
    print("Verified 257 elements in [0,3275], with no nonconstant arithmetic progression of length 3.")
    print("Verified the cardinality gain and the strict inequality for the evaluation point.")


if __name__ == "__main__":
    main()
