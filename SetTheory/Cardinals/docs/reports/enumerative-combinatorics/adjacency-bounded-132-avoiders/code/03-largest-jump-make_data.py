"""Regenerate exact coefficient and small-size enumeration tables."""
from pathlib import Path
from fractions import Fraction as F
import csv
from model import avoiders, catalan, deficit, probability_series

root = Path(__file__).resolve().parents[1]
g, _, _ = probability_series(256)
with (root/'data'/'limit_probabilities.csv').open('w', newline='') as f:
    writer = csv.writer(f)
    writer.writerow(['k', 'probability_numerator', 'probability_denominator',
                     'probability_decimal', 'tail_gt_k_decimal'])
    cdf = F(0)
    for k in range(1, len(g)):
        cdf += g[k]
        writer.writerow([k, g[k].numerator, g[k].denominator,
                         format(float(g[k]), '.16g'), format(float(1-cdf), '.16g')])
with (root/'data'/'finite_histograms.csv').open('w', newline='') as f:
    writer = csv.writer(f)
    writer.writerow(['n', 'deficit', 'count', 'Catalan_n', 'probability'])
    for n in range(2, 13):
        hist = [0]*n
        for p in avoiders(n):
            hist[deficit(p)] += 1
        assert sum(hist) == catalan(n)
        for k in range(1, n):
            writer.writerow([n, k, hist[k], catalan(n), hist[k]/catalan(n)])
with (root/'data'/'extreme_jump_exact.csv').open('w', newline='') as f:
    writer = csv.writer(f)
    writer.writerow(['n', 'probability_numerator', 'probability_denominator',
                     'probability', 'limit_7_over_48'])
    for n in [3, 4, 8, 12, 20, 50, 100, 200, 500, 1000]:
        p = F(catalan(n-2)+sum(catalan(j) for j in range(n-1)), catalan(n))
        writer.writerow([n, p.numerator, p.denominator, float(p), float(F(7,48))])
print('Wrote 256 exact limiting probabilities, histograms n=2..12, and exact extreme-jump probabilities.')
