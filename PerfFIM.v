(** * Performances Tests of the Frequent Itemset Mining Algorithm *)

Require Import Coq.Lists.List ZArith ZArith.Zorder. Import ListNotations.
Require Import SyDPaCC.FIM.SeqFIM SyDPaCC.FIM.Support.HasEqDec SyDPaCC.FIM.DataZoo.

(* 
Section Fim6.

  (** This version uses the [otimes] operator necessary for the
      parallel version, instead of [add]. *)

  Fixpoint tab''' least Vss os t :=
    match os with
    | [] => t
    | o::os =>
      tab''' least Vss os
             (Tree.Par.otimes least t (Tree.Par.to_tree least Vss o))
    end.
  
  Definition fim6 least vss os :=
    if (least <=? length vss)%nat
    then select (tab''' least vss os (Tree.Node([],vss)[]))
    else [].

End Fim6. *)


Module ZHasEqDec <: HasEqDec.
  Definition A := Z.
  Definition eq_dec := Z.eq_dec.
End ZHasEqDec.

Module M := Fim ZHasEqDec.
Import M.

Check fim4.

Definition result0 := fim least vss os.

Definition result1 := fim1 least vss os.

Definition result2 := fim2 least vss [] os.

Definition result3 := at_least least vss (fim3 least vss [] os).

Definition result4 := fim4 least vss os.


(* Definition result5 := fim5 least vss os.

Definition result6_1 :=
  tab''' least vss [1;2;3;4;5;6;7;8;9]%Z (Tree.empty vss).

Definition result6_2 :=
  tab''' least vss [10;11;12;13;14;15;16;17]%Z (Tree.empty vss).

Definition result6 := select(Tree.Par.otimes least result6_1 result6_2). *)

Time Eval vm_compute in result4.

(*
Time Eval vm_compute in result5.

Time Eval vm_compute in result6. *)

Close Scope Z_scope.