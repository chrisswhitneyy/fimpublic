Require Import SyDPaCC.FIM.Support.Le.
Require Import SyDPaCC.FIM.Support.List.
Require Import SyDPaCC.FIM.Support.Tree.
Require Import SyDPaCC.FIM.Support.HasEqDec.
Require Import SyDPaCC.FIM.SeqFIM.
Require Import ZArith.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellZInt.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellZNum.

Extract Inlined Constant Z.eq_dec => "(Prelude.==)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant leb => "(Prelude.<=)".

Extraction Language Haskell.
Separate Extraction SeqFIM.
Separate Extraction PerfFim.

Extraction Language OCaml.
Require Import ExtrOCamllBasic ExtrOcamlZInt ExtrOcamlNatInt.
