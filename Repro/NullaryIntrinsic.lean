import Contracts.Common
verity_intrinsic gasleft () : Verity.Core.Uint256
  where pure;
        yul := builtin "gas";
        min_fork := cancun;
        semantics := (0 : Verity.Core.Uint256);
        obligation [g := assumed "x"]
