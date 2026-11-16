module
public import TemplateNthCore
@[expose] public section
namespace PalomarPA
/-- Explicit Foundation-free HFS indexing formula, assembled from arithmetic
constructor data and fully instantiated syntax templates. -/
def nthFormula : Formula Empty 3 := ConstructedNth.formula
end PalomarPA
