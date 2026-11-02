import DiophantineConsistency.CurrentKernelData2011
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
#eval do
  let p := DiophantineConsistency.CurrentWindowCarry2011.ports
  IO.FS.writeFile "port0.txt" (toString (p 0))
  IO.FS.writeFile "port1.txt" (toString (p 1))
  IO.FS.writeFile "port2.txt" (toString (p 2))
  IO.FS.writeFile "port3.txt" (toString (p 3))
  IO.println "WROTE_FOUR_EXACT_DECIMAL_PORTS"
