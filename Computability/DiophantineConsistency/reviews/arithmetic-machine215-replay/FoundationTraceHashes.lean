import Lake.Build.Trace

def main (args : List String) : IO UInt32 := do
  match args with
  | [listFile] =>
    let paths ← IO.FS.lines listFile
    for p in paths do
      let h ← Lake.computeFileHash p (text := p.endsWith ".lean")
      IO.println s!"{p}\t{h}"
    return 0
  | _ =>
    IO.eprintln "expected one path-list file"
    return 2
