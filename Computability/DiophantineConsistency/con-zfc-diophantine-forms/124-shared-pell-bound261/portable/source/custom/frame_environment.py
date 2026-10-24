from pathlib import Path
import sys
BASE=Path(__file__).resolve().parents[1]/'round14'
sys.path.insert(0,str(BASE/'architecture'))
import build_derived_label_range as dl
h,bp=dl.h,dl.bp
ONE,TWO=h.ONE,h.TWO
FOUR=('c',4)
