import Compiler.CompileDriver
import Safe.Contract

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  IO.FS.createDirAll out
  Compiler.compileSpecsWithOptions [SafeVerity.Safe.spec] out false [] {} none none none (some out)
  pure 0
