# Lean join from the nine-variable seed to the decoded current ports

`NineFreshPorts.current_natural_from_bytes` proves the exact equality

```
ObjectCurrentEquation2011.naturalExpression =
  ObjectCurrentEquation2011.positiveShift
    (ObjectCurrentEquation2011.expressionAt CurrentFourPortBytes.decoded)
```

The unique nine-variable endpoint defines `left` and `right` from the natural split of that `naturalExpression`, and defines its quartic seed from those two sides. The imported `CurrentFourPortBytes.decoded_eq_ports` theorem says the four symbolic big-endian byte lists decode to the current fixed port tuple. Thus this Lean equality joins the current equation source used by the seed to the symbolic byte decoders; it does not read a gzip file, the Markdown transcription or a PDF.

Actual outer session 74890 and both Lean children exited 0. The axiom report for the equality lists only `propext`, `Classical.choice`, and `Quot.sound`. Source hash is `021f31480e76409b970e774b09d050dbdf66e9db3c1da7b8d8f4a0e102902c1b`; runner `cb90d9887f8af5271b0353106499910d8be89d8cc9958d8dd7e6c258b5ae5c70`; state `316e0b2ce1f44b54712fde4bca1b423be88fe792d025af0ab9cbe36cf200050a`; object `ac7a2bcf535e34cb2da731360372ec31d68bab0df648628980a612c6b825effd`.

The preceding [first attempt](../nine-current-fresh-port-join/attempt01/) failed in outer session 36403: Lean could not find `FreshModel106` because its root was omitted from the assembled search path. This retry adds that missing provider root, with the source theorem otherwise unchanged. The runner rechecks the endpoint provider and all 874 recorded tuple guard slots before building, then guards 510 direct candidate slots around this client and clones 1,056 inherited overlay links. Tuple guards are not rechecked after compilation, and no full transitive/dynamic load trace or clean base rebuild is claimed. Lean used one worker, `-M2800`, sampled 4-GiB session RSS, 10-GiB host floor and 120-second timeout; samples may miss transient spikes or escaped processes.
