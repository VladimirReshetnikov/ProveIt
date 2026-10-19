import BusyBeaver.ZFC.CountedTreeRotation240
open SetTheory.BusyBeaver.ZFC
open ControlCatalogue CountedTreeRotation240

#print axioms SetTheory.BusyBeaver.ZFC.CountedTreeRotation240.counted_eq
#print axioms SetTheory.BusyBeaver.ZFC.CountedTreeRotation240.leaf_count
#print axioms SetTheory.BusyBeaver.ZFC.CountedTreeRotation240.catalogue_length

example : counted = annotate TreeRotation240.tree := counted_eq
example : SiteCoverage.leafCount TreeRotation240.tree = 6455 := leaf_count
example : (leafEntries TreeRotation240.tree).length = 6455 := catalogue_length
