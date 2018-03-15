Require Import
        SyDPaCC.FIM.Support.Le
        SyDPaCC.FIM.Support.List
        SyDPaCC.FIM.Support.Tree.
Require Import SyDPaCC.FIM.SeqFIM SyDPaCC.FIM.PerfFIM.
Require Import
        SyDPaCC.FIM.DataZoo
        SyDPaCC.FIM.DataMushroom
        SyDPaCC.FIM.DataRetail1000
        SyDPaCC.FIM.DataRetail2000.
Require Import ZArith.

Extraction Blacklist List String Map Nat.

Extraction Language Ocaml.
Require Import ExtrOcamlBasic.

Separate Extraction DataZoo.
Separate Extraction DataMushroom.
Separate Extraction DataRetail1000.
Separate Extraction DataRetail2000.
Separate Extraction SeqFIM.
Separate Extraction PerfFIM.