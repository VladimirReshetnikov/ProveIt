History-selector discovery searches
===================================

These optional searches discover designs; the accepted SEL theorem is
verified separately by machines/SEL and the written induction proof.
Python 3.10+, standard library only. Run from this directory:

  python3 synthesize_selector.py
  python3 shared_selector193.py

Both scripts read the frozen primary.native.tm alongside them and write
receipts in this directory. The first tries 1,204,352 provider assignments
for 16 history-distinguished pairs, with both choices of retained control.
It accepts 12 labeled tables, representing six graph classes: the supplied
B class and five new single-selector classes. See selector_search.json.
SEL combines two of those new classes; its combined certificate is in
machines/SEL, not inferred from the individual discovery hits.

The second tries four old controls replaced by three, sharing one selector
between two pairs using a tag in the original current cell. It considers
three pair sets, 48 keeper/selector/tag configurations, and 1,787,952
provider assignments, requiring exact old-step endpoints within 31
transitions and within the two-cell local window. No assignment passes.
A stronger search over all 116 disjoint pair choices is supplied separately
in research/lowlevel. Neither negative result is a global state lower bound.

Exterior tape is arbitrary and unaccessed in the accepted two-cell local
certificates. Raw discovery code is not part of the proof's trust base.
