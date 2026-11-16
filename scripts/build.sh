#!/bin/bash
# Compile the Verity Safe to Yul (lake exe safe-compile) and the Yul to EVM creation bytecode,
# out/Safe.bin (read by the Foundry tests).
set -euo pipefail
cd "$(dirname "$0")/.."
SOLC=${SOLC:-solc}
rm -f out/Safe.yul out/Safe.bin
lake build safe-compile >/dev/null
.lake/build/bin/safe-compile out >/dev/null 2>&1 || true   # EvmYul module init prints a harmless python panic
[ -s out/Safe.yul ] || { echo "safe-compile produced no Yul" >&2; exit 1; }
"$SOLC" --strict-assembly --evm-version cancun --optimize --bin out/Safe.yul \
  | awk '/Binary representation:/{getline; print; exit}' | tr -d '\n' > out/Safe.bin
[ -s out/Safe.bin ] || { echo "no bytecode for Safe" >&2; exit 1; }
