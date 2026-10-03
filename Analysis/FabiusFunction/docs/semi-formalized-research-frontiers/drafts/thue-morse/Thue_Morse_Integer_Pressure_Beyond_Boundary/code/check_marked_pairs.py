"""Check labeled-unit pairing counts and the differential k! normalization."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# data/rerun/ in the package, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parents[1] / 'data' / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from functools import lru_cache
from itertools import product
from math import factorial
from fractions import Fraction
from pathlib import Path
import json
@lru_cache(None)
def matchings(alpha,k):
 if k==0:return 1
 if sum(alpha)<2*k:return 0
 i=next((i for i,a in enumerate(alpha)if a),None)
 if i is None:return 0
 a=list(alpha);a[i]-=1
 out=matchings(tuple(a),k)
 for j,v in enumerate(a):
  if j!=i and v:
   b=a.copy();b[j]-=1;out+=v*matchings(tuple(b),k-1)
 return out
@lru_cache(None)
def ordered_derivatives(alpha,k):
 if k==0:return 1
 if sum(alpha)<2*k:return 0
 out=0
 for i in range(len(alpha)):
  for j in range(i+1,len(alpha)):
   if alpha[i] and alpha[j]:
    b=list(alpha);b[i]-=1;b[j]-=1
    out+=alpha[i]*alpha[j]*ordered_derivatives(tuple(b),k-1)
 return out
count=0
for d in range(2,9):
 for s in range((d-2)//2+1):
  q=d+2*s;k=2*s+1
  for colors in range(2,5):
   for alpha in product(range(d),repeat=colors):
    if sum(alpha)!=q:continue
    M=matchings(alpha,k);D=ordered_derivatives(alpha,k)
    assert M>0 and D==factorial(k)*M
    assert k<=min(q//2,q-max(alpha))
    count+=1
out={'all_checks_passed':True,'retained_color_profiles':count,'scope':'Finite supplementary check of the labeled-unit proof, d=2..8 and two to four colors'}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('marked_pair_checks.json', json.dumps(out,indent=2)+'\n')
print('All',count,'marked-pair profiles pass')
