# Restricted local state-fold searches

The C++ sources, exact inputs, logs, and search_receipts.json record fresh
searches for one-state savings. None finds a candidate.

~~~sh
g++ -O3 -std=c++17 search_local.cpp -o /tmp/pa194_local
g++ -O3 -std=c++17 search_coupled.cpp -o /tmp/pa194_coupled
~~~

See each source's short usage line for invocation. Inputs are
primary.native.tm, ormp/machine/machine.native.tm, and
ormp/accelerated/machine.native.tm. Native start is 74 and halt is 254.

Pairs exclude the initial control. Incoming writes/directions supply
two-cell cylinders. A replacement must stay within its cylinder and
reproduce one old step exactly, up to the state alias. The first search
excludes intermediate returns to the merged control and caps length at
32. The coupled search permits those returns with cap 64, synthesizes
only working-state targets, and excludes conflicting overlapping entry
cylinders.

Zero results exclude only this restricted family, not arbitrary quotients,
source-invariant folds, multi-state rewrites, encodings, or initializers.
