"""Compute confluent-column reductions directly in a monic polynomial quotient."""


def multiply(lhs, rhs, polynomial, modulus):
    degree = len(polynomial) - 1
    product = [0] * (2*degree - 1)
    for i, a in enumerate(lhs):
        for j, b in enumerate(rhs):
            product[i+j] += a*b
    for i in range(len(product)-1, degree-1, -1):
        for j in range(degree):
            product[i-degree+j] -= product[i]*polynomial[j]
    return tuple(v % modulus for v in product[:degree])


def prepare(polynomial, prime, period, output):
    one = (1, 0, 0, 0, 0, 0)
    x = (0, 1, 0, 0, 0, 0)
    term = one
    residues = []
    for _ in range(period):
        residues.append(tuple(z % prime for z in term))
        term = multiply(term, x, polynomial, prime**2)
    assert term[0] % prime and all(z % prime == 0 for z in term[1:])
    increment = (0,) + tuple(z//prime for z in term[1:])
    powers = [one]
    for _ in range(4):
        powers.append(multiply(powers[-1], increment, polynomial, prime))
    with open(output, "w") as f:
        print(period, prime, file=f)
        for residue in residues:
            for power in powers:
                column = multiply(residue, power, polynomial, prime)
                # Delete the coordinate already occupied by the fixed column 1.
                print(*column[1:], file=f)
