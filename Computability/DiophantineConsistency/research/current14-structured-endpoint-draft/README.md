# Unchecked structured-port endpoint draft

This is a **Lean source draft, not a checked theorem**. It attempts to join
`Current14LiteralPorts.all_ports` with the standard iPRA endpoint using an
existential port tuple. Its first four conclusions state the existing printed
arithmetic recipes for beta, rational K, mu and omega; its last conclusion is
iPRA derivability for the expression built from that same tuple. The proof
uses the existing current port tuple as witness rather than equating two
large closed finite vectors, which may avoid the kernel memory failure in the
separate [printed-syntax join](../current14-printed-syntax-join/README.md).
No claim is made that it actually avoids that failure until Lean checks it.

A coherent build requires the active 1,000-module endpoint rebuild to pass,
the 61-module [printed-port extension](../current14-printed-port-extension-plan/README.md)
to be authenticated and built, then the existing assembly and this draft to
be compiled against that same coherent provider. Those steps have not yet
happened. The earlier assembly was checked on a different mixed provider and
cannot simply be combined with an arbitrary endpoint overlay. The source may
contain elaboration, namespace, type or memory errors; the selected mapped
refutation predicate and all inherited external ancestry need their normal
interpretation. It does not parse TeX/PDF, bind compressed payloads, prove ZFC
consistent, or exhibit a literal iPRA proof.
