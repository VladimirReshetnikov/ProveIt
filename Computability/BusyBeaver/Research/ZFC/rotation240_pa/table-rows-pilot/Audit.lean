import BusyBeaver.ZFC.TableRowsRotation240Pilot
open SetTheory.BusyBeaver.ZFC
open SiteCoverage TableRowsRotation240Pilot
#print axioms SetTheory.BusyBeaver.ZFC.TableRowsRotation240Pilot.checked
example : allSites check cutPath.reverse (descend TreeRotation240.tree cutPath) = true := checked
