Require Import Coq.Lists.List Program SyDPaCC.Core.Bmf SyDPaCC.Support.Lists.Member.
Require Import SyDPaCC.Support.Lists.Filter Coq.Bool.Bool Omega Permutation.
Require Import ZArith Structures.Orders Structures.GenericMinMax ZAxioms ZMaxMin Logic.
Require Import SyDPaCC.Support.Sig .
Require Import Recdef Coq.Wellfounded.Inverse_Image.
Require Import SyDPaCC.FIM.Support.HasEqDec.
Require Import SyDPaCC.FIM.Support.AOrder.
Import ListNotations.

Open Scope sydpacc_scope.

Set Implicit Arguments.
(* ------------------------------------------------------ *)

(** * Additional Results on List Functions *)

Module List (Import A:HasEqDec).

Lemma max_In:
  forall (l:list nat) n,
    In n l ->
    n <= fold_left Nat.max l 0.
Proof.
  induction l as [ | x xs IH ]; intros n Hn.
  - inversion Hn.
  - destruct Hn as [ Heq | HIn ]; subst;
      rewrite fold_symmetric by auto using Max.max_assoc, Max.max_comm.
    + apply Max.le_max_l.
    + simpl. specialize (IH _ HIn).
      rewrite <- fold_symmetric by auto using Max.max_assoc, Max.max_comm.
      apply Nat.le_trans with (m:=Nat.max x n); auto with arith.
      now apply Nat.max_le_compat_l.
Qed.

Lemma flat_map_map:
  forall A B C (f:B->list C) (g:A->B) l,
    flat_map (compose f g) l = flat_map f (map g l).
Proof.
  induction l; simpl.
  - trivial.
  - rewrite <- IHl. trivial.
Qed.

Lemma flat_map_snoc:
  forall (f:Z -> list Z) (x:Z) (xs:list Z),
    flat_map f ( xs ++ [x] )  =  (flat_map f xs) ++ f x.
Proof.
  induction xs; simpl.
  - rewrite app_nil_r. trivial.
  - rewrite IHxs. apply List.app_assoc.
Qed.

Lemma flat_map_ext:
  forall (A B: Type) (f g : A -> list B),
    (forall a : A, f a = g a) -> forall l : list A, flat_map f l = flat_map g l.
Proof.
  induction l; simpl.
  - trivial.
  - intros. rewrite IHl.
    rewrite H. reflexivity.
Qed.

Lemma flat_map_assumption:
  forall (A B: Type) (f g : A -> list B) l,
    (forall a : A, In a l -> f a = g a) ->
    flat_map f l = flat_map g l.
Proof.
  induction l; simpl.
  - trivial.
  - intros. rewrite IHl.
    rewrite H. reflexivity.
    * left. reflexivity.
    * intros. apply H. right. assumption.
Qed.

Definition f_eq A B (f g:A->B) :=
  forall x:A, f x = g x.

Infix "≡" := f_eq (at level 50, no associativity).

(** Useful properties of map and filter *)
Definition filter_map_prop :
  forall A (a:A) p,
    (filter p) ∘ map (cons a) ≡
               (map (cons a)) ∘ (filter (p ∘ (cons a))).
Proof.
  intros A a p l; induction l as [ | x xs IH];  simpl.
  - trivial.
  - repeat autounfold in *. simpl.
    destruct ( p (a::x) ); simpl.
    + now rewrite IH.
    + assumption.
Qed.

Lemma filter_pipeline_prop:
  forall A (p q:A->bool) l,
    filter p (filter q l) = filter (fun x => andb (p x)(q x)) l.
Proof.
  intros A p q l; induction l as [ | x xs IHl ]; simpl.
  - reflexivity.
  - autounfold in *; simpl.
    destruct (q x) eqn: qa_eqn; simpl.
    + destruct (p x) eqn: pa_eqn; simpl.
      * rewrite IHl. trivial.
      * trivial.
    + destruct (p x) eqn: pa_eqn; simpl.
      * rewrite IHl. trivial.
      * trivial.
Qed.

(** Subs enumerates all the sublists of the object list os *)
Fixpoint subs A (x : list A) : list (list A) :=
  match x with
  | [ ] => [ [ ] ]
  | x :: xs => subs xs ++ (map (cons x) (subs xs))
  end.

Fixpoint sublist A (xs : list A) (ys : list A): Prop :=
  match xs with
  | [ ] => True
  | x :: xs => (sublist xs ys) /\ (In x ys)
  end.

(** subListb: returns true if xs is a sublist (i.e. subset) of ys,
      and false otherwise *)
Fixpoint sublistb A (eq_dec:forall (a b:A),{a = b}+{a <> b})
         (xs : list A) (ys : list A): bool  :=
  match xs with
  | [ ] => true
  | x :: xs => andb (sublistb eq_dec xs ys)(mem eq_dec x ys)
  end.

Lemma sublist_In:
  forall A (l1 l2:list A),
    sublist l1 l2 ->
    (forall x, In x l1 -> In x l2).
Proof.
  intros A; induction l1 as [ | h1 t1 IH]; intros l2 Hsub x Hin.
  - inversion Hin.
  - simpl in Hsub; destruct Hsub as [ Hsub1 Hin1 ].
    simpl in Hin; destruct Hin as [ Heq | Hin ]; subst.
    + trivial.
    + auto using IH.
Qed.

Lemma sublist_dec:
  forall A eq_dec (xs ys:list A),
    sublistb eq_dec xs ys = true <-> sublist xs ys.
Proof.
  intros A eq_dec; induction xs as [ | x xs IH]; intros ys;
    split; intro H; simpl in *; trivial.
  - now rewrite andb_true_iff, <- In_mem_eq, IH in H.
  - now rewrite andb_true_iff, <- In_mem_eq, IH.
Qed.

Lemma sublistb_cons_r:
  forall A eq (xs1 xs2:list A)(x2:A),
    sublistb eq xs1 xs2 = true ->
    sublistb eq xs1 (x2::xs2) = true.
Proof.
  intros A eq; induction xs1 as [|x1 xs1 IH]; intros xs2 x2 H.
  - trivial.
  - simpl in *.
    apply andb_prop in H; destruct H as [ H1 H2 ].
    rewrite IH by auto; simpl.
    destruct(eq x2 x1); auto.
Qed.
Lemma sublistb_app_r:
  forall A eq (xs1 xs2 xs3:list A),
    sublistb eq xs1 xs2 = true ->
    sublistb eq xs1 (xs2++xs3) = true.
Proof.
  intros A eq; induction xs1 as [|x1 xs1 IH]; intros xs2 xs3 H.
  - trivial.
  - simpl in *.
    apply andb_prop in H; destruct H as [ H1 H2 ].
    rewrite IH by auto; simpl.
    apply In_mem_eq, in_or_app.
    apply In_mem_eq in H2; auto.
Qed.

Lemma sublistb_rev_r:
  forall A eq (xs1 xs2:list A),
    sublistb eq xs1 xs2 = true ->
    sublistb eq xs1 (rev xs2) = true.
Proof.
  intros A eq; induction xs1 as [|x1 xs1 IH]; intros xs2 H.
  - trivial.
  - simpl in *.
    apply andb_prop in H; destruct H as [ H1 H2 ].
    rewrite IH by auto; simpl.
    apply In_mem_eq, In_rev; rewrite rev_involutive.
    eapply In_mem_eq; eauto.
Qed.

Lemma sublistb_refl:
  forall A eq (xs:list A), sublistb eq xs xs = true.
Proof.
  intros A eq; induction xs as [|x xs IH]; auto; simpl.
  eapply sublistb_cons_r in IH. rewrite IH; simpl.
  destruct(eq x x); auto.
Qed.

Lemma sublistb_trans:
  forall A eq (xs ys zs: list A),
    sublistb eq xs ys = true ->
    sublistb eq ys zs = true ->
    sublistb eq xs zs = true.
Proof.
  intros A eq; induction xs as [|x xs IH];
    destruct ys as [|y ys];intros zs H1 H2; simpl; auto.
  - simpl in H1; rewrite andb_false_r in H1. discriminate.
  - simpl in H1; apply andb_prop in H1. destruct H1 as [H1 H3].
    erewrite IH; eauto.
    simpl in H2; apply andb_prop in H2. destruct H2 as [H2 H4].
    destruct(eq y x) eqn:Heq; subst.
    + now rewrite H4.
    + assert(mem eq x zs = true) as H.
      {
        apply In_mem_eq. apply In_mem_eq in H3.
        apply sublist_dec in H2.
        now apply (sublist_In _ _ H2).
      }
      now rewrite H.
Qed.

Lemma sublistb_filter:
  forall A eq p (l:list A),
    sublistb eq (filter p l) l = true.
Proof.
  intros A eq p l; induction l as [|h t IH]; trivial; simpl.
  destruct(p h).
  - simpl. destruct(eq h h); try contradiction.
    rewrite andb_true_r.
    now apply sublistb_cons_r.
  - now apply sublistb_cons_r.
Qed.

Lemma sublistb_app:
  forall A dec xs (l1 l2:list A),
    sublistb dec (l1++l2) xs =
    (sublistb dec l1 xs) && (sublistb dec l2 xs).
Proof.
  intros A dec xs; induction l1 as [ | h1 t1 IH]; intros l2.
  - trivial.
  - simpl; rewrite IH.
    repeat rewrite <- andb_assoc.
    f_equal. apply andb_comm.
Qed.

Lemma filter_sublistb_length:
  forall A eq_dec xs (l1 l2:list A),
    sublist l1 l2 ->
    length( filter (sublistb eq_dec l2) xs ) <=
    length( filter (sublistb eq_dec l1) xs ).
Proof.
  intros A eq_dec; induction xs  as [ | x xs IH]; intros l1 l2 H; auto; simpl.
  destruct(sublistb eq_dec l1 x) eqn:Hsub1;
    destruct(sublistb eq_dec l2 x) eqn:Hsub2; simpl.
  - apply Peano.le_n_S. now auto using IH.
  - constructor. now auto using IH.
  - assert(sublistb eq_dec l1 x = true) as H'
        by (rewrite <- sublist_dec with (eq_dec:=eq_dec) in H;
            eapply sublistb_trans; eauto).
    rewrite H' in Hsub1.
    discriminate.
  - now auto using IH.
Qed.

Lemma filter_func_prop:
  forall (A:Type) l,
    filter (fun _ : list A => true) l = l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma filter_ext:
  forall (A : Type) (f g : A -> bool),
    f ≡ g ->
    filter f ≡ filter g.
Proof.
  intros A f g H l; induction l; simpl.
  - trivial.
  - intros. rewrite IHl.
    rewrite H. reflexivity.
Qed.

Lemma filter_assumption:
  forall (A : Type) (f g : A -> bool) l,
    (forall x, In x l -> f x = g x) ->
    filter f l = filter g l.
Proof.
  intros A f g l H; induction l as [ | h t IH ].
  - trivial.
  - simpl. rewrite IH.
    + now rewrite H by now left.
    + intros x HIn.
      apply H. now right.
Qed.

Lemma filter_comm:
  forall A (p q:A->bool) l,
    filter p (filter q l) = filter q (filter p l).
Proof.
  intros A p q l.
  repeat rewrite filter_pipeline_prop.
  apply filter_ext.
  intro x; apply andb_comm.
Qed.

Lemma filter_length:
  forall (A:Type) p (l:list A),
    length (filter p l) <=  length l.
Proof.
  induction l; simpl.
  - trivial.
  - destruct (p a) eqn: pa.
    + simpl. omega.
    + constructor. assumption.
Qed.

Hint Rewrite filter_length: length.

Fixpoint map_sig A (P:A->Type)(f:A -> sigT P)(l:list A) : list (sigT P) :=
  match l with
  | [] => []
  | h::t => (f h)::map_sig f t
  end.

Lemma map_map_sig:
  forall A B (P:A->Type)(f:A->sigT P)(g:sigT P->B)(xs:list A),
    map g (map_sig f xs) = map (g∘f) xs.
Proof.
  intros A B P f g; induction xs as [ | x xs IH ].
  - trivial.
  - simpl; f_equal; now rewrite IH.
Qed.

Lemma map_sig_length:
  forall A (P:A->Type)(f:A -> sigT P)(l:list A),
    length(map_sig f l) = length l.
Proof.
  intros A P f; induction l as [ | x xs IH ]; auto; simpl; auto using IH.
Qed.

Hint Rewrite map_sig_length: length.

Lemma map_sig_proj:
  forall A (P:A->Type)(f:A->sigT P)(l:list A)
    (H: forall x, projT1(f x) = x),
    map (@projT1 _ P) (map_sig f l) = l.
Proof.
  intros A P f; induction l as [ | x xs IH]; intro H.
  - trivial.
  - simpl; now rewrite H, IH.
Qed.

Lemma nth_map_sig:
  forall A (P:A->Type)(f:A->sigT P) pos (l:list A)  fd d,
    pos < length l ->
    nth pos (map_sig f l) fd =
    f (nth pos l d).
Proof.
  intros A P f; induction pos as [ | pos IH ]; destruct l as [ | x xs ];
    intros fd d H;  simpl in H; try omega.
  - trivial.
  - simpl; erewrite IH; eauto with arith.
Qed.

Lemma sig_nth_map_sig:
  forall A (P:A->Type)(f:A->sigT P) l (pos:nat|pos<length(map_sig f l)),
    Sig.nth (map_sig f l) pos =
    f (Sig.nth l  (Sig.cast_sig pos (Sig.length_sig (map_sig_length f l)))).
Proof.
  intros A P f; induction l as [ | x xs IH ];
    intros  [ pos Hpos ]; destruct pos as [ | pos ]; simpl in *; try omega; auto.
  rewrite IH.
  erewrite Sig.nth_pi; eauto.
Qed.

Lemma sublist_app_l :
  forall A (l1 l2:list A),
    sublist l1 (l2 ++ l1).
Proof.
  induction l1.
  - simpl. trivial.
  - intros l2. simpl.
    split.
    + replace (l2 ++ a :: l1) with ((l2++[a])++l1)
        by (rewrite <- List.app_assoc; now simpl).
      apply IHl1.
    + firstorder.
Qed.

Ltac In_empty :=
  match goal with
  | [H: List.In _ [] |- _] =>inversion H
  | [H: Exists _ [] |- _ ] =>
    apply Exists_exists in H;
    let x := fresh "x" in
    destruct H as [x [ H _ ] ];
    inversion H
  end.

End List.

Module Type ListOrder (Import A: HasEqDec) (Import AOrder : AOrder A).

  Module Import List := List A.

  Fixpoint is_sorted (zs:list A) : bool :=
    match zs with
    | [ ] => true
    | z::zs =>
      match zs with
      | [] => true
      | z'::zs' => if AOrder.leb z z'
                  then is_sorted zs
                  else false
      end
    end.

  (** list membership where the list sorted **)
  Fixpoint isElement (a:A) (l:list A) : bool :=
    match l with
    | [ ] => false
    | h :: t => if A.eq_dec h a
               then true
               else if AOrder.leb a h
                    then false
                    else isElement a t
    end.
  
  Lemma mem_isElement:
    forall zs, is_sorted zs = true ->
          forall z, mem A.eq_dec z zs = isElement z zs.
  Proof.
  induction zs as [ | z zs IH ]; intros Hsorted z0.
  - reflexivity.
  - simpl in *.
    destruct(A.eq_dec z z0) as [ H | H] eqn:Hdec.
    + trivial.
    +  destruct zs as [ | z'' zs].
       * destruct (leb z0 z); auto.
       * set (zs':= z'' :: zs) in *.
         rewrite IH by ( destruct ( leb z z''); auto; discriminate).
         unfold zs'; simpl.
         destruct (A.eq_dec z'' z0); destruct (leb z0 z'') eqn:HH;
           destruct(leb z z'') eqn:HHH; subst ; auto ; try discriminate.
         --- apply AOrder.leb_le in HH; apply AOrder.leb_le in HHH.
             assert (Hnot:not (le z0 z)). {
               intro x. assert (z = z0) by now apply le_antisym. auto.
               
             }
             apply AOrder.leb_nle in Hnot.
             now rewrite Hnot.
         --- apply AOrder.leb_nle in HH.
             assert (le z0 z0) by apply le_refl.
             apply HH in H0. intuition.
         --- destruct (leb z0 z); trivial. 
         --- apply AOrder.leb_nle in HH; apply AOrder.leb_le in HHH.
             assert(Hnot: not(le z0 z)). {
               contradict HH. now apply le_trans with (y := z).
               
             }
             apply AOrder.leb_nle in Hnot.
             now rewrite Hnot.
  Qed.
 
End ListOrder.

Close Scope sydpacc_scope.
