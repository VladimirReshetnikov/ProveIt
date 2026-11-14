"""Rebuild the two coupled-fold inputs from the ternary local-window data."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
with (ROOT/'ternary_fold_input.txt').open() as f:
    count,radius,_=map(int,f.readline().split())
    labels=list(map(int,f.readline().split()))
    rest=f.read()
for state,prefix in [(62,'tail62'),(68,'halt68')]:
    with (ROOT/f'{prefix}_fold_input.txt').open('w') as f:
        f.write(f'{count} {labels.index(state)} {radius} 240\n')
        f.write(' '.join(map(str,labels))+'\n')
        f.write(rest)
