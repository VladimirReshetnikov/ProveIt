"""Verify the explicit additive witness and truncation margin with integers."""
from collections import Counter
from math import factorial

dimension = 9
base = 11
digits = range(6)
cutoff = 3**20
radius = 105
displaced = 2**20

# counts[s] counts all digit vectors with centered squared norm s.
counts = Counter({0: 1})
for coordinate in range(dimension):
    following = Counter()
    for norm, count in counts.items():
        for digit in digits:
            following[norm + (2 * digit - 5)**2] += count
    counts = following

solutions = [(i, j, dimension - i - j) for i in range(dimension + 1)
             for j in range(dimension - i + 1)
             if i + 9*j + 25*(dimension - i - j) == radius]
multinomial = sum(factorial(9) // (factorial(i)*factorial(j)*factorial(k))
                  for i, j, k in solutions)
maximum_encoding = max(digits) * (base**dimension - 1) // (base - 1)
assert sum(counts.values()) == 6**9
assert counts[radius] == 2**9 * multinomial == 1_053_696
assert counts[radius] > displaced
assert 2 * maximum_encoding < cutoff
assert 2 * max(digits) < base
assert 1023**2 * counts[radius] > 1024**2 * displaced
print('Centered squared norm:', radius)
print('Number of vectors:', counts[radius])
print('Number of displaced ternary deficits:', displaced)
print('Largest encoding in the full digit box:', maximum_encoding)
print('Ternary cutoff:', cutoff)
