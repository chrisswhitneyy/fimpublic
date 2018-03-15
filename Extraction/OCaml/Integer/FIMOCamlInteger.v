Require Import
        SyDPaCC.FIM.Support.Le
        SyDPaCC.FIM.Support.List
        SyDPaCC.FIM.Support.Tree.
Require Import SyDPaCC.FIM.SeqFIM SyDPaCC.FIM.PerfFIM.
Require Import SyDPaCC.FIM.DataZoo.
Require Import ZArith.

Extraction Blacklist List String Map.

Extraction Language Ocaml.
Require Import ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatBigInt.

Extract Inlined Constant Z.leb => "Big_int.le_big_int".
Extract Inlined Constant Z.ltb => "Big_int.lt_big_int".
Extract Inlined Constant Z.eq_dec => "Big_int.eq_big_int".
Extract Inlined Constant leb => "Big_int.le_big_int".

Separate Extraction DataZoo.
Separate Extraction SeqFIM.
Separate Extraction PerfFIM.

