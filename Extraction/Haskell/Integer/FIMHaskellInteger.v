Require Import
        SyDPaCC.FIM.Support.Le
        SyDPaCC.FIM.Support.List
        SyDPaCC.FIM.Support.Tree.
Require Import SyDPaCC.FIM.SeqFIM SyDPaCC.FIM.PerfFIM.
Require Import SyDPaCC.FIM.DataZoo.
Require Import ZArith.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZNum.

Extract Inlined Constant Z.eq_dec => "(Prelude.==)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant leb => "(Prelude.<=)".

Extraction Language Haskell.
Separate Extraction DataZoo.
Separate Extraction SeqFIM.
Separate Extraction PerfFIM.


