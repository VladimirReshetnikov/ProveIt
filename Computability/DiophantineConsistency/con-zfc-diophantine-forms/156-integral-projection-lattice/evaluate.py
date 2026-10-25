#!/usr/bin/env python3
"""Evaluate a supplied complete integer polynomial at an integer tuple."""
from pathlib import Path
import argparse,json,math
ROOT=Path(__file__).resolve().parent
PROFILES={
 "gram-balanced":"gram/balanced/equation.json",
 "gram-lowheight":"gram/lowheight/equation.json",
 "sos-balanced":"projection/shared240_balanced/equation.json",
 "sos-lowheight":"projection/shared240_lowheight/equation.json",
 "factorialfree":"projection/factorialfree241/equation.json",
}
def main():
 p=argparse.ArgumentParser()
 p.add_argument("--profile",choices=PROFILES,default="gram-balanced")
 p.add_argument("point",type=Path)
 a=p.parse_args()
 eq=json.loads((ROOT/PROFILES[a.profile]).read_text())
 x=json.loads(a.point.read_text())
 if not isinstance(x,list) or len(x)!=len(eq["variables"]) or any(type(v) is not int for v in x):
  raise ValueError("Expected exactly "+str(len(eq["variables"]))+" integers")
 r=[sum(c*math.prod(x[i] for i in m) for c,m in row["terms"])
    for row in eq["residuals"]]
 value=sum(v*v for v in r)+sum(s*r[i]*r[j] for i,j,s in eq.get("gram_cross_terms",[]))
 print(json.dumps({"profile":a.profile,"integer_value":value,
                   "is_zero":value==0,"nonzero_residuals":sum(v!=0 for v in r)}))
if __name__=="__main__":main()
