from probe_macros import *
from collections import Counter,defaultdict
basepath=base/'docs/pa194_conpa_2026-11-13/construction'
grammar=c.read_grammar(basepath/'source/pa194.grammar.json')
inc=('leaf','inc',1)
def expanded(t):
 if t=='node60':return (inc,inc)
 if t=='node61':return ((inc,inc),(inc,inc))
 return tuple(map(expanded,t)) if c.isnode(t) else t
def word(t):return word(t[0])+word(t[1]) if c.isnode(t) else [t]
w=word(expanded(grammar))
if __name__=='__main__':
 for i,x in enumerate(w):print(i,x)
