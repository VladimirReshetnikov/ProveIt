"""Independently replay every rational center through finite nested sums.

The producer holder.py uses differential recurrences.  This checker instead
parses each factor into a multiple sum, evaluates that sum by cumulative
inner sums, and compares the resulting rational number exactly.  It imports
only the Q(i) arithmetic type from the producer.  It recomputes the tail
budget directly from the displayed binomial formula.
"""

from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json
import sys
import time

from holder import Gaussian, ZERO, ONE

if hasattr(sys,"set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def finite_nested_gpl(word, cutoff):
    if not word:
        return ONE
    weights,letters=[],[]
    zero_run=0
    for a in word:
        if a==ZERO:
            zero_run+=1
        else:
            weights.append(zero_run+1)
            letters.append(a)
            zero_run=0
    if zero_run:
        raise ValueError("The finite nested series cannot end in a zero letter")
    arguments=[Gaussian(Q(1,2))/letters[0]]
    arguments.extend(letters[j-1]/letters[j] for j in range(1,len(letters)))
    inner=[ONE]*(cutoff+1)
    for weight,z in reversed(list(zip(weights,arguments))):
        cumulative=[ZERO]*(cutoff+1)
        power=ONE
        for n in range(1,cutoff+1):
            power*=z
            cumulative[n]=cumulative[n-1]+power*inner[n-1]/(n**weight)
        inner=cumulative
    return (-1)**len(letters)*inner[cutoff]


def tail_bound(d,n):
    return Q(sum(comb(n,j) for j in range(min(d,n+1))),2**n) if d else Q(0)


def replay(record):
    word=tuple(Gaussian(Q(x),Q(y)) for x,y in record["word"])
    n=record["cutoff"]
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError("The cutoff must be a nonnegative integer")
    if type(record["prefactor"]) is not int or record["prefactor"] not in (-1,1):
        raise ValueError("Certificates only admit prefactor +1 or -1")
    if word and (word[0] == ONE or word[-1] == ZERO):
        raise ValueError("The word violates an endpoint condition")
    for a in word:
        if a not in (ZERO,ONE) and not (
                a.re*a.re+a.im*a.im >= 1 and
                (1-a.re)**2+a.im*a.im >= 1):
            raise ValueError("The word contains a letter outside the proved domain")
    center,radius=ZERO,Q(0)
    for j in range(len(word)+1):
        left=tuple(ONE-a for a in reversed(word[:j]))
        right=word[j:]
        center+=(-1)**j*finite_nested_gpl(left,n)*finite_nested_gpl(right,n)
        radius+=tail_bound(sum(a!=ZERO for a in left),n)
        radius+=tail_bound(sum(a!=ZERO for a in right),n)
    center*=record["prefactor"]
    expected=Gaussian(*(Q(v) for v in record["center"]))
    if center != expected:
        raise ValueError("Exact center disagreement")
    if radius != Q(record["radius"]):
        raise ValueError("Exact tail budget disagreement")
    return True


def main():
    path=Path(__file__).resolve().parents[1]/"results"
    records=json.loads((path/"rational_certificates.json").read_text())
    start=time.perf_counter()
    checks=[]
    for name,record in records.items():
        replay(record)
        checks.append({"name":name,"center_equal":True,"radius_equal":True})
    result={"method":"independent finite nested sums for each Hoelder factor",
            "checks":checks,"count":len(checks),
            "elapsed_seconds":round(time.perf_counter()-start,3)}
    (path/"replay_summary.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="checks"},indent=2))


if __name__=="__main__":
    main()
