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

Require Import ExtrHaskellBasic.

Extraction Language Haskell.
Separate Extraction DataZoo.
Separate Extraction DataMushroom.
Separate Extraction DataRetail1000.
Separate Extraction DataRetail2000.
Separate Extraction SeqFIM.
Separate Extraction PerfFIM.