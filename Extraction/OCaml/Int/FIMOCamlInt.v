Require Import
        SyDPaCC.FIM.Support.Le
        SyDPaCC.FIM.Support.List
        SyDPaCC.FIM.Support.Tree.
Require Import SyDPaCC.FIM.SeqFIM SyDPaCC.FIM.PerfFIM.
Require Import SyDPaCC.FIM.DataZoo.
Require Import Arith.
Require Import ZArith.

Extraction Blacklist List String Map.

Extraction Language Ocaml.
Require Import ExtrOcamlBasic ExtrOcamlZInt ExtrOcamlNatInt.

Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Z.ltb => "(<)".
Extract Inlined Constant Z.eq_dec => "(=)".
Extract Inlined Constant leb => "(<=)".

Separate Extraction DataZoo.
Separate Extraction SeqFIM.
Separate Extraction PerfFIM.

