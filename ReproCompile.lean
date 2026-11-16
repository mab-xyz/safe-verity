import Compiler.CompileDriver
import Repro.EventArray
def main (args : List String) : IO UInt32 := do
  let out := args.headD "out-repro"
  IO.FS.createDirAll out
  Compiler.compileSpecsWithOptions [Repro.EventArray.spec] out false [] {} none none none (some out)
  pure 0
