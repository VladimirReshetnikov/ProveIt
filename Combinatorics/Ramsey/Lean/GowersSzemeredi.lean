import GowersSzemeredi.Definitions
import GowersSzemeredi.Sections01_03
import GowersSzemeredi.Section04
import GowersSzemeredi.Section05
import GowersSzemeredi.Sections06_07
import GowersSzemeredi.Sections08_09
import GowersSzemeredi.Section10
import GowersSzemeredi.Sections12_13
import GowersSzemeredi.Sections14_15
import GowersSzemeredi.Section16
import GowersSzemeredi.Sections17_18
import GowersSzemeredi.ProofInfrastructure
import GowersSzemeredi.Proofs01Headline
import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs02Uniformity
import GowersSzemeredi.Proofs03Basic
import GowersSzemeredi.Proofs03Equivalences
import GowersSzemeredi.Proofs03Cubes
import GowersSzemeredi.Proofs05FourierInterval
import GowersSzemeredi.Proofs05Progressions
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs07DRC
import GowersSzemeredi.Proofs09Moments
import GowersSzemeredi.Proofs10Counting
import GowersSzemeredi.Proofs10Bohr
import GowersSzemeredi.Proofs10Error
import GowersSzemeredi.Proofs10Induced
import GowersSzemeredi.Proofs10Shift
import GowersSzemeredi.Proofs12
import GowersSzemeredi.Proofs13Basic
import GowersSzemeredi.Proofs14Fourier
import GowersSzemeredi.Proofs14Configurations
import GowersSzemeredi.Proofs14Arrangements
import GowersSzemeredi.Proofs14HigherArrangements
import GowersSzemeredi.Proofs14Product
import GowersSzemeredi.Proofs15LevelSets
import GowersSzemeredi.Proofs15Walsh
import GowersSzemeredi.Proofs15Walsh2
import GowersSzemeredi.Proofs16Basic
import GowersSzemeredi.Proofs17FinitePatterns

/-!
# Gowers's proof of Szemerédi's theorem: statement catalogue

This facade exposes the auxiliary definitions, conjectures, and every numbered
result in W. T. Gowers's *A new proof of Szemerédi's theorem*.

Following the repository's statement-catalogue convention, each paper result
is a definition with value in `Prop`; completed formal proofs are exported as
companion theorems with the suffix `_holds`.  The definitions themselves add
no axioms or assertions to Lean's trusted environment.
-/
