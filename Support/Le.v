Require Import Coq.Lists.List Program SyDPaCC.Core.Bmf SyDPaCC.Support.Lists.Member.
Require Import SyDPaCC.Support.Lists.Filter Coq.Bool.Bool Omega Permutation.
Require Import ZArith Structures.Orders Structures.GenericMinMax ZAxioms ZMaxMin Logic.
Require Import SyDPaCC.Support.Sig.
Require Import Recdef Coq.Wellfounded.Inverse_Image.
Import ListNotations.

Set Implicit Arguments.

(** ** Uniqueness Proof for le *)
Require Import Eqdep_dec.

  Fact eq_rect_eq_nat :
    forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
  Proof.
    intros.
    apply (K_dec_set eq_nat_dec) with (p:=h).
    reflexivity.
  Qed.

  Scheme le_ind' := Induction for le Sort Prop.

  Theorem le_uniqueness_proof : forall (n m : nat) (p q : n <= m), p = q.
  Proof.
    induction p using le_ind'; intro q.
    replace (le_n n) with
    (eq_rect n (fun n0 => n <= n0) (le_n n) n (refl_equal n)).
    2:reflexivity.
    generalize (refl_equal n).

    pattern n at 2 4 6 10, q.
    case q; [intro | intros m l e].
    rewrite <- eq_rect_eq_nat; trivial.
    contradiction (le_Sn_n m); rewrite <- e; assumption.
    replace (le_S n m p) with
    (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).
    2:reflexivity.
    generalize (refl_equal (S m)).
    pattern (S m) at 1 3 4 6, q. case q; [intro Heq | intros m0 l HeqS].
    contradiction (le_Sn_n m); rewrite Heq; assumption.
    injection HeqS; intro Heq; generalize l HeqS.
    rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
    rewrite (IHp l0); reflexivity.
  Qed.
