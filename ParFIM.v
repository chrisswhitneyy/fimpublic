(** * Parallelization of the Frequent Itemset Mining Algorithm *)

Require Import SyDPaCC.Core.Bmf SyDPaCC.Core.Parallelization.
Require Import SyDPaCC.FIM.SeqFIM.

Require SyDPaCC.Bsml.Model.Core SyDPaCC.Bsml.Model.Pid 
        SyDPaCC.Bsml.DataStructures.DistributedList
        SyDPaCC.Bsml.DataStructures.DistributedVector
        SyDPaCC.Bsml.Skeletons.StdLib
        SyDPaCC.Bsml.Skeletons.Accumulate.

Open Scope sydpacc_scope.

Module Make (Import Bsml: Core.BSML).

  Module Pid  := Pid.Make Bsml.Bsp.
  Module PL   := DistributedList.C Bsml Pid.
  Module DV   := DistributedVector.C Bsml Pid.
  Module StdLib := StdLib.Make Bsml Pid.
  Module Skel   := Accumulate.Make Bsml Pid StdLib PL DV. 

  (* TO MODIFY AND COMPLETE: 
  
  Instance diffusion_accumulate_tail
           `(g:B->C) `(q:A->B) `{Ht:Monoid B otimes e_otimes} (c:B) :
    Opt (  )
        ( g ∘ (otimes c) ∘ (fun l=>fold_left (fun s t=>otimes s (q t)) l e_otimes) ).
  Proof.
    constructor; intro xs; autounfold; simpl.
    generalize dependent c.
    induction xs as [ | x xs IH ]; intro c.
    - simpl. now rewrite right_neutral.
    - simpl. rewrite IH.
      repeat rewrite fold_left_map_r with (g:=q).
      repeat rewrite <- fold_left_prop by typeclasses eauto.
      now rewrite @left_neutral with (e:=e_otimes),
                                     @right_neutral with (e:=e_otimes)
      by typeclasses eauto.
  Qed.
   
  (** ** Version where the result is a scalar *)
  Definition par_ms : par(list N.t) -> img Mps.ms_spec :=
    Eval sydpacc in 
      parallel (hom_to_map_reduce Mps.ms_spec).

   *)
  
End Make.

Close Scope sydpacc_scope.