Require Import Coq.Lists.List Coq.Bool.Bool Omega Permutation.
Require Import ZArith Structures.Orders Structures.GenericMinMax.
Require Import ZAxioms ZMaxMin Logic.
Require Import Recdef Coq.Wellfounded.Inverse_Image.
Import ListNotations.
Require Import SyDPaCC.Core.Bmf SyDPaCC.Support.List SyDPaCC.Support.Sig.
Require Import SyDPaCC.FIM.Support.List SyDPaCC.FIM.Support.HasEqDec.

Set Implicit Arguments.

(* ------------------------------------------------------ *)

(** * A Tree Data Structure for Tabluation Transformation *)

Module Tree (Import A:HasEqDec).

  Module Import List := List A.

(** Tree data type *)
(* Note: could be changed to Node: list Z -> list(list Z) -> list tree -> tree *)
Inductive tree : Type  :=
| Node : (list A  * list( list A)) -> list tree -> tree.

(** Tree induction principle *)
Lemma tree_induction:
  forall (P: tree->Prop),
    (forall r vss ts, (forall t, List.In t ts -> P t) -> P (Node (r,vss) ts)) ->
    (forall t,P t).
Proof.
  intros P H. fix 1; intro t; destruct t as [ [r vss] ts].
  apply H. intros t Hin.
  induction ts as  [  | t' ts' IH ]; simpl in Hin; inversion Hin.
  - rewrite <- H0; trivial.
  - now apply IH.
Qed.

(** Access functions *)
Definition root_of (t:tree) :=
  match t with
  | Node (r,_) _ => r
  end.

Definition vss_of (t:tree) :=
  match t with
  | Node (_,vss) _ => vss
  end.

Definition children (t:tree) :=
  match t with
  | Node _ ts => ts
  end.

Definition tree_split:
  forall t, t = Node(root_of t, vss_of t)(children t).
Proof.
  now destruct t using tree_induction.
Qed.


(** Tree member relations: node, subset, strict subtree *)
Inductive NodeIn : (list A * (list (list A))) -> tree -> Prop :=
| In_root : forall r vss ts,
    NodeIn (r , vss) (Node (r,vss) ts)
| In_childern : forall r vss r0 vss0 ts0,
    Exists (NodeIn (r,vss)) ts0 ->
    NodeIn (r,vss) (Node (r0,vss0) ts0).

Inductive In : tree -> tree -> Prop :=
| _root : forall t,
    In t t
| _children : forall t r vss ts t',
    List.In t' ts ->
    In t t' ->
    In t (Node (r,vss) ts).

Fact In_refl: forall t, In t t.
Proof. constructor. Qed.

Lemma ListIn_In_trans:
  forall t r0 vss0 ts0 t1,
    List.In t1 ts0 ->
    In (Node(r0,vss0)ts0) t ->
    In t1 t.
Proof.
  induction t as [ r vss ts IH ] using tree_induction.
  intros r0 vss0 ts0 t1 H H0; inversion H0; clear H0; subst.
  - econstructor 2; eauto.
    now constructor.
  - econstructor 2; eauto.
Qed.

Fact In_trans:
  forall t1 t2 t3, In t1 t2 -> In t2 t3 -> In t1 t3.
Proof.
  intros t1 t2 t3 H1; generalize dependent t3;
    induction H1; intros t3 H2; inversion H2; subst;
      try solve [ econstructor; eauto ].
  eapply IHIn, ListIn_In_trans; eauto.
Qed.

Inductive Sub: tree -> tree  -> Prop :=
| _subtree_direct:
    forall t r vss ts,
      List.In t ts ->
      Sub t (Node (r,vss) ts)
| _subtree_indirect:
    forall t t' r vss ts,
      List.In t' ts ->
      Sub t t' ->
      Sub t (Node (r,vss) ts).

Lemma ListIn_Sub_trans:
  forall t r0 vss0 ts0 t1,
    List.In t1 ts0 ->
    Sub (Node(r0,vss0)ts0) t ->
    Sub t1 t.
Proof.
  induction t as [ r vss ts IH ] using tree_induction.
  intros r0 vss0 ts0 t1 H H0; inversion H0; clear H0; subst.
  - econstructor 2; eauto.
    now constructor.
  - econstructor 2; eauto.
Qed.

Lemma Sub_In:
  forall t t', Sub t' t -> In t' t.
Proof.
  intros t t' H; induction H; subst.
  - econstructor; eauto; constructor.
  - econstructor; eauto.
Qed.

Lemma Sub_trans:
  forall t1 t2 t3,
    Sub t1 t2 -> Sub t2 t3 ->
    Sub t1 t3.
Proof.
  intros t1 t2 t3 H1 H2; induction H1; inversion H2; subst.
  - eapply ListIn_Sub_trans; eauto.
  - eapply ListIn_Sub_trans; eauto.
  - eapply IHSub; eapply ListIn_Sub_trans; eauto.
  - eapply IHSub; eapply ListIn_Sub_trans; eauto.
Qed.

Lemma In_Sub_trans:
  forall t1 t2 t3,
    In t1 t2 -> Sub t2 t3 ->
    Sub t1 t3.
Proof.
  intros t1 t2 t3 H1 H2; induction H1; inversion H2; subst; trivial.
  - eapply IHIn. eapply ListIn_Sub_trans; eauto.
  - eapply IHIn; eapply ListIn_Sub_trans; eauto.
Qed.

Lemma Sub_NodeIn:
  forall t t', Sub t' t ->
               NodeIn (root_of t', vss_of t') t.
Proof.
  intros t t' H; induction H.
  - constructor. destruct t as [ [r0 vss0] ts0]; simpl.
    apply Exists_exists; eexists; split; eauto; econstructor.
  - constructor. apply Exists_exists; eexists; eauto.
Qed.

Lemma NodeIn_In:
  forall t r' vss', NodeIn (r',vss') t <->
                    exists ts', In (Node (r',vss') ts') t.
Proof.
  induction t as [ r vss ts IH ] using tree_induction; intros r' vss'; split; intro  H.
  - inversion H; subst.
    + eexists; econstructor.
    + apply Exists_exists in H1. destruct H1 as [t'' [HIn HNodeIn ] ].
      specialize (IH t'' HIn r' vss').
      destruct IH as [IH1 _]. specialize (IH1  HNodeIn).
      destruct IH1 as [ ts' Hts'].
      eexists; econstructor; eauto.
  - destruct H as [ts' H]; inversion H; subst.
    + constructor.
    + constructor. apply Exists_exists; eexists; split; eauto.
      apply IH; auto; eexists; eauto.
Qed.


(** Functions specific to the Frequent Itemset Mining application *)

(** Adds the object [o] to the tabulation tree [t] *)
Fixpoint add least o t : tree :=
  match t with
  | Node (r,vss) ts =>
    let o_vss := filter (mem A.eq_dec o) vss in
    if Nat.leb least (length o_vss) then
      Node (r,vss) ([Node (r++[o], o_vss) []] ++ map (add least o) ts)
    else t
  end.

(** Tree invariants *)
Definition I1 least (t:tree) : Prop :=
  forall r' vss', NodeIn (r',vss') t -> least <= length vss'.

Definition I2 vss (t:tree) : Prop :=
  forall r' vss', NodeIn (r',vss') t ->
             vss' = filter (List.sublistb A.eq_dec r') vss.

Definition I3 (t:tree) : Prop :=
  forall ti tj,  Sub tj ti -> In ti t ->
                 match tj, ti with
                 | Node (rj,vssj) tsj , Node(ri,vssi) tsi =>
                     (sublist ri rj) (* could be strict *)
                   /\ (sublist vssj vssi)
                 end.

Inductive Inv least vss t :=
| _Inv : I1 least t -> I2 vss t -> I3 t ->
         Inv least vss t.

Hint Unfold I1 I2 I3 : fim.

Lemma Sub_sublist_root:
  forall t, I3 t ->
       forall t', Sub t' t ->
             sublist (root_of t) (root_of t').
Proof.
  autounfold with fim. intros t H t' H'.
  assert(In t t) as Hin by constructor.
  specialize (H _ _ H' Hin).
  destruct t as [ [r vss] ts];
    destruct t' as [ [r' vss'] ts'];
    now destruct H as [ H1 H2 ].
Qed.

Lemma Sub_sublist_vss:
  forall t, I3 t ->
       forall t', Sub t' t ->
             sublist (vss_of t') (vss_of t).
Proof.
  autounfold with fim. intros t H t' H'.
  assert(In t t) as Hin by constructor.
  specialize (H _ _ H' Hin).
  destruct t as [ [r vss] ts];
    destruct t' as [ [r' vss'] ts'];
    now destruct H as [ H1 H2 ].
Qed.

Lemma Sub_lt_least:
  forall least Vss o t,
    I3 t ->
    length (filter (mem A.eq_dec o) (filter (List.sublistb A.eq_dec (root_of t)) Vss)) < least ->
    forall t', Sub t' t ->
          least <=? length(filter (List.sublistb A.eq_dec (root_of t')) (filter (mem A.eq_dec o) Vss))
          = false.
Proof.
  intros least Vss o t H H0 t' H1.
  apply Nat.leb_nle, Nat.nle_gt.
  eapply le_lt_trans. eapply filter_sublistb_length; eauto.
  - eapply Sub_sublist_root; eauto.
  - now rewrite filter_comm.
Qed.

Lemma Inv_at_least:
  forall least Vss (t:tree), Inv least Vss t -> least <= length (vss_of t).
Proof.
  intros least Vss [ [ r vss ] ts ] [ H1 H2].
  autounfold in H1; eapply H1; econstructor.
Qed.

Ltac nodein H :=
  intros; eapply H; constructor;
  apply Exists_exists; eexists; eauto.

Ltac Ee :=
  match goal with
  | [ H: Exists _ _ |- _] =>
    apply Exists_exists in H;
    let x := fresh "x" in
    let Hx := fresh "Hx" in
    destruct H as [ x [ Hx H ] ]
  end.

Ltac cons_list :=
  match goal with
  | [ H: List.In _ (_::_) |- _ ] =>
    let Heq := fresh "Heq" in
    let Hin := fresh "Hin" in
    destruct H as [ Heq | Hin ]; subst
  end.

(** Proof that all of the children of a tree satisfy the invarariants *)
Lemma Inv_children :
  forall least Vss t, Inv least Vss t ->
                 forall t', List.In t' (children t) -> Inv least Vss t'.
Proof.
  intros least Vss [ [ r vss ] ts ] [ Ht Ht' Ht''] t Hin; constructor;
    autounfold with fim in *.
  - nodein Ht.
  - nodein Ht'.
  - intros; eapply Ht''; eauto.
    econstructor; eauto.
Qed.

(** Proof that all of the subtrees in a tree satisfy the invarariants *)
Lemma Inv_Sub : forall least Vss t,
    Inv least Vss t -> forall t', Sub t' t -> Inv least Vss t'.
Proof.
  intros least Vss [ [ r vss ] ts ] [ Ht Ht' Ht''] t HSub; constructor;
    autounfold with fim in *.
  - intros r' vss' H. eapply Ht.
    apply NodeIn_In in H. destruct H as [ ts' HIn ].
    assert(Sub (Node(r',vss') ts') (Node(r,vss) ts))  as HSub'
        by (eapply In_Sub_trans; eauto).
    set(S:=Sub_NodeIn HSub'). simpl in S.
    eauto.
  - intros r' vss' H. eapply Ht'.
    apply NodeIn_In in H. destruct H as [ts' HIn].
    apply NodeIn_In; eexists.
    eapply Sub_In, In_Sub_trans; eauto.
  - intros ti tj H H0. eapply Ht''; eauto.
    apply Sub_In.
    eapply In_Sub_trans; eauto.
Qed.

Lemma Inv_In : forall least Vss t,
    Inv least Vss t -> forall t', In t' t -> Inv least Vss t'.
Proof.
  intros least Vss [ [ r vss ] ts ] [ Ht Ht' Ht''] t HSub; constructor;
    autounfold with fim in *.
  - intros r' vss' H. eapply Ht.
    apply NodeIn_In in H. destruct H as [ ts' HIn ].
    assert(In (Node(r',vss') ts') (Node(r,vss) ts))  as HSub'
        by (eapply In_trans; eauto).
    apply NodeIn_In; eexists; eauto.
  - intros r' vss' H. eapply Ht'.
    apply NodeIn_In in H. destruct H as [ts' HIn].
    apply NodeIn_In; eexists; eauto.
    eapply In_trans; eauto.
  - intros ti tj H H0. eapply Ht''; eauto.
    eapply In_trans; eauto.
Qed.

Lemma new_o_Inv1:
  forall least Vss o r vss ts,
    Inv least Vss (Node(r,vss)ts) ->
    (forall t, List.In t ts -> I1 least (add least o t)) ->
    (least <=? length (filter (mem A.eq_dec o) vss) = true) ->
    I1 least (Node(r,vss) ([Node(r++[o],filter(mem A.eq_dec o) vss)[]]++map(add least o) ts)).
Proof.
  intros least Vss o r vss ts HInv IH Hleast.
  intros r' vss' H; inversion H; subst.
  - eapply HInv; econstructor.
  - Ee; cons_list.
    + inversion H1; subst; try In_empty.
      now apply Nat.leb_le in Hleast.
    + apply in_map_iff in Hin; destruct Hin as [ t0 [ Ht0 Hin ] ]; subst.
      set(Hc := Inv_children HInv t0 Hin).
      specialize (IH _ Hin).
      eapply IH; eauto.
Qed.


Lemma add_Inv1:
  forall least Vss t o, Inv least Vss t -> I1 least (add least o t).
Proof.
  induction t as [ r vss ts IH ] using tree_induction;
    intros  o Hinv; simpl; autounfold with fim in *.
  destruct(least <=? length (filter (mem A.eq_dec o) vss)) eqn:Hleast.
  - intros. eapply new_o_Inv1; eauto.
    unfold I1; intros. eapply IH; eauto.
    eapply Inv_children; eauto.
  - apply Hinv.
Qed.

Lemma I2_at_root:
  forall Vss r vss ts,
    I2 Vss (Node(r,vss)ts) -> vss = filter (List.sublistb A.eq_dec r) Vss.
Proof.
  intros Vss r vss ts H. autounfold with fim in *.
  eapply H; constructor.
Qed.

Lemma new_o_Inv2:
  forall least Vss o r vss ts,
    Inv least Vss (Node(r,vss)ts) ->
    (forall t, List.In t ts -> I2 Vss (add least o t)) ->
    (least <=? length (filter (mem A.eq_dec o) vss) = true) ->
    I2 Vss (Node(r,vss) ([Node(r++[o],filter(mem A.eq_dec o) vss)[]]++map(add least o) ts)).
Proof.
  intros least Vss o r vss ts HInv IH Hleast.
  intros r' vss' H; inversion H; subst; clear H.
  - (* at root *) eapply HInv; constructor.
  - Ee; cons_list.
    + (* new child (adding o) *)
      inversion H1; subst; try In_empty.
      rewrite I2_at_root with (Vss:=Vss)(vss:=vss)(r:=r)(ts:=ts) by apply HInv.
      assert(filter (List.sublistb A.eq_dec (r++[o])) Vss =
             filter (fun l=>(List.sublistb A.eq_dec r l)&&(List.sublistb A.eq_dec [o] l)) Vss) as H
          by (apply filter_ext; intro l; apply List.sublistb_app).
      rewrite H.
      rewrite <- filter_pipeline_prop, filter_comm.
      reflexivity.
    + (* recursive call on the children *)
      apply in_map_iff in Hin; destruct Hin as [t' [ Heq Hin ]]; subst.
      eapply IH; eauto.
Qed.

Lemma add_Inv2:
  forall least Vss t o, Inv least Vss t -> I2 Vss (add least o t).
Proof.
  induction t as [ r vss ts IH ] using tree_induction;
    intros  o HInv; simpl; autounfold with fim in *;
      intros r' vss' H.
  destruct(least <=? length (filter (mem A.eq_dec o) vss)) eqn:Hleast'.
  - eapply new_o_Inv2; eauto.
    unfold I2; intros; eapply IH; eauto.
    eapply Inv_children; eauto.
  - now apply HInv.
Qed.

Lemma new_o_Inv3:
  forall least Vss o r vss ts,
    Inv least Vss (Node(r,vss)ts) ->
    (forall t, List.In t ts -> I3 (add least o t)) ->
    (least <=? length (filter (mem A.eq_dec o) vss) = true) ->
    I3 (Node(r,vss) ([Node(r++[o],filter(mem A.eq_dec o) vss)[]]++map(add least o) ts)).
Proof.
  intros least Vss o r vss ts HInv IH Hleast.
  unfold I3; intros ti tj H H0.
  inversion H0; subst; clear H0.
  - inversion H; subst; clear H; cons_list.
    + split.
      * apply sublist_dec with(eq_dec:=A.eq_dec).
        rewrite <- rev_involutive with (l:=r++[o]).
        apply List.sublistb_rev_r. rewrite rev_app_distr; simpl.
        apply List.sublistb_cons_r. apply List.sublistb_rev_r, List.sublistb_refl.
      * apply (sublist_dec (list_eq_dec A.eq_dec)), List.sublistb_filter.
    + set(Hin':=Hin).
      apply in_map_iff in Hin'; destruct Hin' as [ t0 [ Ht0 Hin' ] ]; subst.
      assert(Sub t0 (Node(r,vss)ts)) as Hsub by now constructor.
      destruct t0 as [ [ r0 vss0 ] ts0 ]; simpl in *;
        destruct( least <=? length (filter (mem A.eq_dec o) vss0));
        destruct HInv as [ Ht Ht' Ht''];
        specialize(Ht'' _ _ Hsub (_root _)); simpl in Ht'; trivial.
    + inversion H5; subst; clear H5; In_empty.
    + set(Hin':=Hin).
      apply in_map_iff in Hin'; destruct Hin' as [ t0 [ Ht0 Hin' ] ]; subst.
      assert(H: Inv least Vss t0) by (eapply Inv_children; eauto).
      destruct t0 as [ [ r0 vss0 ] ts0 ]; simpl in *.
      assert(sublist r0 (root_of tj) /\ sublist (vss_of tj) vss0) as HH.
      {
        specialize (IH _ Hin' _ _ H5 (_root _)).
        rewrite (tree_split tj) in IH.
        destruct( least <=? length (filter (mem A.eq_dec o) vss0));
          simpl in *;auto.
      }
      assert(Sub (Node(r0,vss0)ts0) (Node(r,vss)ts)) as Hsub
          by (constructor; auto).
      assert(sublist r r0 /\ sublist vss0 vss) as HH'.
      {
        destruct HInv as [ Ht Ht' Ht''].
        specialize(Ht'' (Node(r,vss)ts) (Node(r0,vss0)ts0) Hsub (_root _)).
        now simpl in Ht''.
      }
      destruct HH as [ HH1 HH2]; destruct HH' as [ HH3 HH4].
      rewrite (tree_split tj); repeat split.
      * apply sublist_dec with(eq_dec:=A.eq_dec).
        apply sublist_dec with(eq_dec:=A.eq_dec) in HH1.
        apply sublist_dec with(eq_dec:=A.eq_dec) in HH3.
        eapply List.sublistb_trans; eauto.
      * apply sublist_dec with(eq_dec:=list_eq_dec A.eq_dec).
        apply sublist_dec with(eq_dec:=list_eq_dec A.eq_dec) in HH2.
        apply sublist_dec with(eq_dec:=list_eq_dec A.eq_dec) in HH4.
        eapply List.sublistb_trans; eauto.
  - cons_list.
    + inversion H6; subst; try In_empty.
      inversion H; subst; try In_empty.
    + apply in_map_iff in Hin; destruct Hin as [ t0 [Heq Ht0] ].
      assert(HH: I3 t') by (rewrite <- Heq; apply IH; auto).
      now apply HH.
Qed.

Lemma add_Inv3:
  forall least Vss t o, Inv least Vss t -> I3 (add least o t).
Proof.
    induction t as [ r vss ts IH ] using tree_induction;
      intros  o Hinv; simpl; autounfold with fim in *.
    intros ti tj H H0.
    destruct(least <=? length (filter (mem A.eq_dec o) vss)) eqn:Hleast'.
    - eapply new_o_Inv3; eauto; unfold I3.
      intros. eapply IH; eauto.
      eapply Inv_children; eauto.
    - apply Hinv; auto.
Qed.

Lemma new_o_Inv:
  forall least Vss o r vss ts,
    Inv least Vss (Node(r,vss)ts) ->
    (forall t, List.In t ts -> Inv least Vss (add least o t)) ->
    (least <=? length (filter (mem A.eq_dec o) vss) = true) ->
    Inv least Vss (Node(r,vss) ([Node(r++[o],filter(mem A.eq_dec o) vss)[]]++map(add least o) ts)).
Proof.
  intros least Vss o r vss ts H IH Hleast; constructor.
  - eapply new_o_Inv1; intros; eauto; now apply IH.
  - eapply new_o_Inv2; intros; eauto; now apply IH.
  - eapply new_o_Inv3; intros; eauto; now apply IH.
Qed.

(** Proof that the application of the add function to tree t
    preserves the invariant *)
Lemma add_Inv:
  forall least Vss t o, Inv least Vss t -> Inv least Vss (add least o t).
Proof.
  intros least Vss t o H; constructor.
  - eapply add_Inv1; eauto.
  - eapply add_Inv2; eauto.
  - eapply add_Inv3; eauto.
Qed.

(** * Size of trees *)

Fixpoint size_tree t : nat :=
  match t with
  | Node (_) ts =>(1 + (fold_left plus (map size_tree ts) 0))%nat
  end.

Fact size_tree_S:
  forall t, 0 < size_tree t.
Proof.
  intros [ [r vss] ts]; simpl.
  auto with arith.
Qed.

Lemma size_In:
  forall t1 t2,
    In t1 t2 ->
    size_tree t1 <= size_tree t2.
Proof.
  intros t1 t2 H; induction H as [ t | t r vss ts t' Hin Hintree IH ].
  - auto.
  - apply in_split in Hin; destruct Hin as [ ts1 [ ts2 Hst ] ]; subst.
    simpl; rewrite map_app, fold_left_app, fold_symmetric by auto with arith; simpl.
    omega.
Qed.

Lemma size_subtree:
  forall t1 t2,
    Sub t1 t2 ->
    size_tree t1 < size_tree t2.
Proof.
  intros t1 t2 H; unfold lt; simpl in *.
  induction H as [ t r vss ts Hin | t t' r vss ts Hin Hsub IH ];
    apply in_split in Hin; destruct Hin as [ts' [ ts'' ] ]; subst; simpl;
      rewrite map_app, fold_left_app, fold_symmetric by auto with arith; simpl;
        omega.
Qed.

Lemma Inv_leaf:
  forall least Vss r vss,
    vss = filter (List.sublistb A.eq_dec r) Vss ->
    least <= length vss ->
    Inv least Vss (Node (r,vss) []).
Proof.
  intros least Vss r vss Hvss Hleast; constructor; autounfold with fim.
  - intros r' vss' H; inversion H; subst; auto.
    apply Exists_exists in H1; destruct H1 as [ x [ Hx _ ]].
    inversion Hx.
  - intros r' vss' H; inversion H; subst; auto; In_empty.
  - intros ti tj H H0; inversion H0; subst.
    + inversion H; subst; In_empty.
    + In_empty.
Qed.

Definition Leaf least Vss r vss H1 H2 :=
  exist _  (Node (r,vss) []) (@Inv_leaf least Vss r vss H1 H2).

Definition empty vss :=
  Node([],vss)[].

Hint Unfold empty: fim.

Lemma Inv_empty least vss :
  least <= length vss ->
  Inv least vss (empty vss).
Proof.
  intros H. apply Inv_leaf; auto; simpl.
  rewrite filter_true; auto.
Qed.

End Tree.

