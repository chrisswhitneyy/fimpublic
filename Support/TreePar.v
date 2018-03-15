Require Import Coq.Lists.List Coq.Bool.Bool Omega Permutation.
Require Import ZArith Structures.Orders Structures.GenericMinMax.
Require Import ZAxioms ZMaxMin Logic.
Require Import Recdef Coq.Wellfounded.Inverse_Image.
Import ListNotations.
Require Import SyDPaCC.Core.Bmf SyDPaCC.Support.List SyDPaCC.Support.Sig.
Require Import SyDPaCC.FIM.Support.List SyDPaCC.FIM.Support.Tree SyDPaCC.FIM.Support.HasEqDec.

Set Implicit Arguments.

Module ParTree (Import A:HasEqDec). (* Stuff needed only for the parallel version *)

  Open Scope sydpacc_scope.

  Module Import Tree := Tree A.

  Section LeastVss.

    Parameter least : nat.
    Parameter Vss : list (list A).

  (** Combination of two tabulation trees: auxiliary and main function *)
Fixpoint add_node least r2 t1 :=
  match t1 with
  | Tree.Node (r1, vss1) ts1 =>
    let vss1' := filter (List.sublistb A.eq_dec r2) vss1 in
    if least <=? length vss1'
    then
      [ Node (r2++r1, vss1') (List.flat_map (add_node least r2) ts1) ]
    else [ ] (* Node (r1,vss1) ts1 *)
  end.


Fixpoint otimes least t1 t2 :=
  match t1 with
  | Node(r1, vss1) ts1 =>
    let t2' := add_node least r1 t2 in
    match t2' with
    | [] => t1
    | (Node(r2, vss2) ts2)::_ =>
      Node(r2, vss2) (ts2++(List.map (fun t1=>otimes least t1 t2) ts1))
    end
  end.

(** Converts an object to a tabluation tree *)
Definition to_tree least vss o :=
  let o_vss := filter (mem A.eq_dec o) vss in
  if least <=? length o_vss
  then Node ([],vss) [Node([o], o_vss) [] ]
  else Node ([],vss) [].


Lemma add_node_nil:
  forall least t, I1 least t -> add_node least [] t = [ t ].
Proof.
  autounfold.
  intros least; induction t  using tree_induction; intro Ht; simpl.
  rewrite filter_true by auto.
  assert(least <=? length vss = true) as Hlen.
  { rewrite Nat.leb_le. eapply Ht. constructor. }
  rewrite Hlen. do 2 f_equal.
  rewrite List.flat_map_assumption with (g:=fun x=>[x]).
  - clear. induction ts; auto; simpl. now rewrite IHts.
  - intros t' Ht'. apply H; auto.
    intros r' vss' H'.
    eapply Ht. constructor.
    apply Exists_exists; exists t'; eauto.
Qed.

Lemma otimes_neutral_right:
  forall least vss t, I1 least t -> I2 vss t ->
                 otimes least t (empty vss) = t.
Proof.
  autounfold with fim; intros least vss; induction t  using tree_induction;
    intros Ht Ht'; simpl.
  assert(vss0 = filter (List.sublistb A.eq_dec r) vss)
    by (apply Ht'; constructor).
  assert(least <=? length vss0 = true) as Hlen.
  {
    rewrite Nat.leb_le. eapply Ht.
    constructor.
  }
  subst.
  rewrite Hlen; simpl.
  rewrite map_assumption with (g:=id).
  - now rewrite map_id, app_nil_r.
  - intros x H0. autounfold; simpl. apply H; auto.
    + nodein Ht.
    + nodein Ht'.
Qed.

Lemma otimes_neutral_left:
  forall least vss t, I1 least t -> I2 vss t ->
                 otimes least (empty vss) t = t.
Proof.
  autounfold with fim; intros least vss;
    induction t  using tree_induction; intros Ht' Ht; simpl.
  assert(vss0 = filter (List.sublistb A.eq_dec r) vss)
    by (apply Ht; constructor).
  subst.
  rewrite filter_true by auto.
  destruct(least <=? length (filter (List.sublistb A.eq_dec r) vss)) eqn:Hleast.
  - simpl. f_equal; rewrite app_nil_r; auto.
    rewrite List.flat_map_assumption with (g:=fun x=>[x]).
    + clear; induction ts; auto; simpl; now rewrite IHts.
    + intros; apply add_node_nil; auto;
      autounfold with fim; nodein Ht'.
  - set(vss_r := filter (List.sublistb A.eq_dec r) vss) in *.
    assert(NodeIn (r,vss_r) (Node (r,vss_r) ts))
      as Hin by constructor.
    specialize (Ht' r vss_r Hin).
    apply Nat.leb_nle in Hleast.
    contradiction.
Qed.

Lemma otimes_not_least:
  forall least Vss o t, Inv least Vss t ->
    length (filter (mem A.eq_dec o) (filter (List.sublistb A.eq_dec (root_of t)) Vss)) < least ->
    (forall t', Sub t' t ->
           otimes least t' (Node ([], Vss) [Node ([o], filter (mem A.eq_dec o) Vss) []]) = t').
Proof.
  intros least Vss o t [ Ht Ht' Ht''] Hleast t' Hsub.
  set(H:= Sub_lt_least Vss o Ht'' Hleast Hsub).
  induction t' as [ r' vss' ts' IH ] using tree_induction;simpl in *.
  simpl in H; rewrite H, app_nil_r; simpl.
  destruct(least <=? length (filter (List.sublistb A.eq_dec r') Vss)); simpl.
  - f_equal.
    + f_equal; symmetry; autounfold with fim in Ht'; apply Ht'.
      set(HH:= Sub_NodeIn Hsub);simpl in HH; apply HH.
    +  rewrite <- map_id; apply map_assumption.
       intros t'' Hin. apply IH; auto.
       assert(Sub t'' (Node(r',vss')ts')) by now constructor.
       destruct t as [ [r vss] ts ]. inversion Hsub;subst.
       * constructor 2 with (t':=Node(r',vss') ts'); auto.
       * eapply ListIn_Sub_trans; eauto.
  - auto.
Qed.

Lemma add_otimes_to_tree:
  forall least Vss o t, Inv least Vss t ->
    otimes least t (to_tree least Vss o) = add least o t.
Proof.
  intros least Vss o;
    induction t as [ r vss ts IH] using tree_induction;
    intros [ Ht Ht' Ht'' ]; autounfold with fim in *; simpl.
  unfold to_tree in *; simpl.

  assert(vss = filter (List.sublistb A.eq_dec r) Vss)
    by (apply Ht'; constructor). subst.

  assert(least <=? length (filter (List.sublistb A.eq_dec r) Vss) = true)
    as Hleast2.
  { apply Nat.leb_le. eapply Ht. constructor. }

  destruct(least<=? length(filter(mem A.eq_dec o) Vss)) eqn:Hleast1; simpl.
  - rewrite Hleast2, app_nil_r.
    rewrite List.filter_comm.
    destruct( least <=?
              length (filter (mem A.eq_dec o)
                             (filter (List.sublistb A.eq_dec r) Vss)))
            eqn:Hleast.
    + f_equal. simpl. f_equal.
      apply map_assumption.
      intros; apply IH; auto; constructor; autounfold with fim.
      * nodein Ht.
      * nodein Ht'.
      * intros; eapply Ht'';auto;econstructor; eauto.
    + simpl. f_equal. rewrite <- map_id.
      apply map_assumption. intros x Hx.
      eapply otimes_not_least; eauto; simpl.
      * constructor; autounfold with fim; eauto.
      * now apply Nat.leb_nle, Nat.nle_gt in Hleast.
      * now constructor.
  - rewrite Hleast2, app_nil_r; simpl.
    assert(least <=? length (filter (mem A.eq_dec o)
                                    (filter (List.sublistb A.eq_dec r) Vss)) = false)
      as Hleast3.
    {
      apply Nat.leb_nle.
      apply Nat.leb_nle in Hleast1.
      contradict Hleast1.
      assert(length (filter (mem A.eq_dec o) (filter (List.sublistb A.eq_dec r) Vss))
             <= length (filter (mem A.eq_dec o) Vss)) as Hlen
          by (rewrite List.filter_comm;apply List.filter_length).
      omega.
    }
    rewrite Hleast3. repeat rewrite app_nil_r. f_equal.
    rewrite <- map_id. apply map_assumption.
    intros; apply otimes_neutral_right; autounfold with fim.
    + nodein Ht.
    + nodein Ht'.
Qed.

Lemma filter_list_sublistb_app:
  forall A eq_decA xs (l1 l2:list A),
    filter(List.sublistb eq_decA (l1++l2)) xs =
    filter(List.sublistb eq_decA l1)(filter (List.sublistb eq_decA l2) xs).
Proof.
  intros A eq xs l1 l2.
  rewrite List.filter_pipeline_prop.
  apply List.filter_ext; intro l.
  apply List.sublistb_app.
Qed.

Ltac destruct_if :=
  match goal with
  | [H: ?X = _ |- context[if ?X then _ else _] ] => rewrite H
  | [ |- context[if ?X then _ else _] ] =>
    let eqn := fresh "least" in  destruct X eqn:eqn
  end.

Ltac filter_eta :=
  match goal with
  | [ H : context [ filter (fun x => ?F x) _ ] |- _ ] =>
    rewrite List.filter_ext with(f:=fun x=>F x)(g:=F) in H by (intro;auto)
  | [ |-  context [ filter (fun x => ?F x ) _ ] ] =>
    rewrite List.filter_ext with(f:=fun x=>F x)(g:=F) by (intro;auto)
  | [ H:  context [ filter (fun x => ?F x && ?G x) _ ] |- _ ] =>
    rewrite <- List.filter_pipeline_prop in H
  | [ |-  context [ filter (fun x => ?F x && ?G x) _ ] ] =>
    rewrite <- List.filter_pipeline_prop
  | [ H:  context [ filter (List.sublistb ?Eq (?l1++?l2)) _ ] |- _ ] =>
    rewrite filter_list_sublistb_app with (eq_decA:=Eq) in H
  | [ |-  context [ filter (List.sublistb ?Eq (?l1 ++ ?l2)) _ ] ] =>
    rewrite filter_list_sublistb_app with (eq_decA:=Eq)
  end.

Ltac filter_order F1 F2 F3 :=
  match goal with
  | [ |- context [ filter F2 (filter F1 _) ] ] =>
    rewrite List.filter_comm with (p:=F2)
  | [ |- context [ filter F3 (filter F1 _) ] ] =>
    rewrite List.filter_comm with (p:=F3)
  | [ |- context [ filter F3 (filter F2 _) ] ] =>
    rewrite List.filter_comm with (p:=F3)
  | [ H:context [ filter F2 (filter F1 _) ] |- _ ] =>
    rewrite List.filter_comm with (p:=F2) in H
  | [ H:context [ filter F3 (filter F1 _) ] |- _ ] =>
    rewrite List.filter_comm with (p:=F3) in H
  | [ H: context [ filter F3 (filter F2 _) ] |- _ ] =>
    rewrite List.filter_comm with (p:=F3) in H
  end.


Ltac simpl_eq :=
  match goal with
  | [ |- filter ?f ?l = filter ?g ?l ] =>
    apply List.filter_ext; intro l
  | [ |- Node _ _ = Node _ _ ] => f_equal
  | [ |- cons _ _ = cons _ _ ] => f_equal
  | [ |- (_, _) = (_, _) ] => f_equal
  end.

Ltac to_prop :=
  match goal with
  | [  H: leb _ _ = true |- _ ] =>
    apply Nat.leb_le in H
  | [  H: leb _ _ = false |- _ ] =>
    apply Nat.leb_nle in H; apply Nat.nle_gt in H
  end.


Fact tool1:
  forall o1 o2 o3 vss,
    length(filter (mem A.eq_dec o1)(filter (mem A.eq_dec o2)(filter (mem A.eq_dec o3) vss)))
    <= length(filter (mem A.eq_dec o2)(filter (mem A.eq_dec o3) vss)).
Proof.
  intros; apply List.filter_length.
Qed.

Lemma otimes_associative_weak:
  forall least vss o1 o2 o3 , least <=? length vss = true ->
    otimes least (to_tree least vss o1)
           (otimes least (to_tree least vss o2) (to_tree least vss o3)) =
    otimes least (otimes least (to_tree least vss o1) (to_tree least vss o2))
           (to_tree least vss o3).
Proof.
  intros least vss o1 o2 o3 H; unfold to_tree.
  repeat (repeat filter_eta;
          repeat filter_order (mem A.eq_dec o1)
                 (mem A.eq_dec o2) (mem A.eq_dec o3);
          destruct_if; simpl in *;
          repeat rewrite (filter_true (fun x=>true)) in * by auto);
    repeat (simpl_eq; symmetry; repeat filter_eta; symmetry);
    try discriminate;
    assert(least < least) as HH
        by(apply Nat.leb_le in least7;
           apply Nat.leb_nle in least3;
           pose(tool1 o1 o2 o3 vss); omega);
    now apply Nat.lt_irrefl in HH.
Qed.

Ltac lt_least :=
  match goal with
  | [H: ?e < _ |- _]=> apply le_lt_trans with (m:=e); auto
  end.

Ltac least_le l :=
  match goal with
  | [H: _ <= length ( filter ?f l )  |- _ ]=>
    apply le_trans with (m:=length(filter f l)); auto
  end.

Ltac find_l :=
  match goal with
  | [ |- _ <= length ?l ] => least_le l; apply List.filter_length
  end.

Definition build least vss l :=
  List.fold_left (fun t o=>add least o t) l (Node([],vss)[]).

Lemma Inv_build:
  forall least vss l,
    least <= length vss ->
    Inv least vss (build least vss l).
Proof.
  intros least vss; induction l as [ | o os IH ] using rev_ind;
    intro H; unfold build in *; simpl.
  - now apply Inv_empty.
  - rewrite <- fold_left_rev_right.
    rewrite rev_unit; simpl.
    rewrite fold_left_rev_right.
    now apply add_Inv, IH.
Qed.

Ltac inv :=
  repeat to_prop;
  match goal with
  | [ |- Inv _ _ (build _ _ _) ] => apply @Inv_build; auto
  | [ |- Inv _ _ (empty _ ) ] => apply @Inv_empty; auto
  | [ |- I1 _ (build _ _ _) ] =>
    apply @Inv_build; auto
  | [ |- I2 _ (build _ _ _) ] =>
    apply @Inv_build; auto
  | [ |- I3 (build _ _ _) ] =>
    apply @Inv_build; auto
  | [ |- I1 _ (empty _) ] =>
    apply @Inv_empty; auto
  | [ Hleast : ?least <= length _  |- I2 _ (empty ?vss) ] =>
    pose(@Inv_empty least vss Hleast) as H;
    destruct H as [ _ H _]; auto
  | [ |- I3 (empty _) ] =>
    repeat to_prop; apply @Inv_empty; auto
  | [ |- I1 _ (add _ _ _) ] =>
    eapply add_Inv1; eauto
  | [ |- I2 _ (add _ _ _) ] =>
    eapply add_Inv2; eauto
  end.

Lemma build_simpl:
  forall least vss x xs,
    build least vss (xs++[x]) =
    add least x (build least vss xs).
Proof.
  intros least vss x xs; unfold build.
  rewrite <- fold_left_rev_right.
  rewrite rev_unit; simpl.
  now rewrite fold_left_rev_right.
Qed.

Lemma build_simpl':
  forall least vss x xs,
    least <= length vss ->
    build least vss (xs++[x]) =
    otimes least (build least vss xs) (build least vss [x]).
Proof.
  intros least vss x xs Hleast.
  rewrite build_simpl.
  rewrite <- add_otimes_to_tree with (Vss:=vss) by inv.
  f_equal.
Qed.

(*
Lemma build_simpl'':
  forall least vss xs x,
    least <= length vss ->
    build least vss (x::xs) =
    otimes least (build least vss [x]) (build least vss xs).
Proof.
  induction xs as [| x xs IH]using rev_ind; intros x' H.
  - admit. (* OK *)
  - replace(x'::xs++[x]) with ((x'::xs)++[x]) by apply app_comm_cons.
    repeat rewrite build_simpl' by auto.
    rewrite IH by auto.
Admitted.
*)

Lemma fold_left_assumption:
  forall A B op op' (l:list B) (e:A),
    (forall x y, (exists lx, x = fold_left op lx e) -> op x y = op' x y) ->
    fold_left op l e = fold_left op' l e .
Proof.
  induction l as [ | x xs IH]; intros e H.
  - trivial.
  - simpl. rewrite IH.
    + f_equal. apply H.
      exists []; auto.
    + intros x0 y H0.
      apply H.
      destruct H0 as [lx Hlx]; subst.
      now exists (x::lx).
Qed.

Lemma otimes_build:
  forall  least vss xs y ys,
    least <= length vss ->
    otimes least (build least vss xs) (build least vss (y::ys)) =
    otimes least (build least vss (xs++[y])) (build least vss ys).
Proof.
Admitted.

Lemma build_build:
  forall least vss,
    least <= length vss ->
    forall l2 l1,
      otimes least (build least vss l1) (build least vss l2) =
      build least vss (l1++l2).
Proof.
  intros least vss H; induction l2 as [|h2 t2 IH]; intro l1.
  - replace (build least vss []) with (empty vss) by now unfold build,empty.
    rewrite otimes_neutral_right by inv.
    now rewrite app_nil_r.
  - rewrite otimes_build by auto.
    rewrite IH.
    f_equal; now rewrite <- app_assoc.
Qed.

Proposition otimes_associative_build:
  forall least (vss:list(list A)),
    least <= length vss ->
    forall l1 l2 l3,
    let t1 := build least vss l1 in
    let t2 := build least vss l2 in
    let t3 := build least vss l3 in
    otimes least t1 (otimes least t2 t3) =
    otimes least (otimes least t1 t2) t3.
Proof.
  intros least vss Hleast l1 l2 l3 t1 t2 t3;
    unfold t1, t2, t3. clear t1 t2 t3.
  repeat rewrite build_build by auto.
  f_equal; apply app_assoc.
Qed.

  End LeastVss.

  Close Scope sydpacc_scope.

End ParTree.