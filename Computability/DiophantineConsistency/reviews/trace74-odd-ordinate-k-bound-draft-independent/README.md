# Independent source review: odd-ordinate k bound

Reviewed unchecked `research/trace74-odd-ordinate-bound-draft/Trace74OddOrdinateKBound.lean` SHA-256 `e27478ee3be30e5fa9e453439029850015ec01c02beac988f7052b51ab616d0d`. It retains the same ports/valuation, positive beta and components, and actual 74 zero. Assuming its imported, as-yet-unaccepted `graph_ordinate_lower`, positivity of v9 gives v8<k=v8+v9; hence c=kY+v8<k(Y+1), and discrete successor yields c+1≤k(Y+1). Substituting A=Y(X+1) gives the stated bound `4(Y(X+1)+1)^2≤k(Y+1)`.

No hidden F/C or reverse guard was found. The argument is mathematically consistent conditional on the imported theorem. Lean elaboration, `change`, successor-order rewrites and resource behavior remain unchecked; no Lean was run. It is a graph-zero consequence, not a graph-zero existence or F/C bound, and requires a separately accepted compatible parent object with captured provider/ancestry scope.
