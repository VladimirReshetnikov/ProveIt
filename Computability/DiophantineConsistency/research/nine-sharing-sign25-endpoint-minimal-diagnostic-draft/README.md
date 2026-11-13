# Sign25 minimal command, alias, and attributes diagnostic draft

Each of these independent modules imports the same previously checked sign25
bridge, with the same source path and resource limits as the failed endpoint.
They separately add a `#check`, a typed expression alias without local
irreducibility attributes, and local irreducibility attributes without an
alias. This compares the individual pieces of the failed second split stage;
the fail-stop runner will not try later pieces after a failure. Importing the
bridge still leaves Lean close to its interpreter memory threshold. Passing or
failing a diagnostic does not prove an endpoint or establish the precise
trigger of the earlier run.
