Require Import Coq.Lists.List Program Coq.Bool.Bool Omega Permutation.
Require Export RelationClasses.
Require Import SyDPaCC.Core.Bmf SyDPaCC.Support.List SyDPaCC.Support.Sig.
Require Import Coq.Wellfounded.Inverse_Image.
Import ListNotations.
From  SyDPaCC.FIM.Support Require Import Tree Le List HasEqDec AOrder.

Set Implicit Arguments.

Generalizable All Variables.

Open Scope sydpacc_scope.

(* ------------------------------------------------------ *)

(** * Misc. Definitions and Properties *)

(** ** Iteration function *)
Fixpoint iter (A:Type) (n:nat) (F:A->A) (g:A) {struct n}  : A :=
  match n with
  | 0 => g
  | S p => F (iter p F g)
  end.

Fact proj1_sig_cast_sig:
  forall A (P P':A->Prop) H (x:A|P x),
    @proj1_sig _ P' (Sig.cast_sig x H)=proj1_sig x.
Proof.
  intros A P P' H x.
  unfold Sig.cast_sig; destruct x.
  reflexivity.
Qed.

(* ------------------------------------------------------ *)

(** * Frequent Itemset Mining Problem *)

(** The frequent set problem goes as follow, given a set of items and
    a large collection of subsets of these items,find the items that
    appear together frequently (exceeding a threshold) in the
    subsets. *)


Module Type FIM (Import A:HasEqDec).

  Module Import List := List A.
  Module Import Tree := Tree A.

  Section FimLeast.

  Variable least : nat.


  (** ** Specification of the Frequent Set problem as defined by Hu 2012. *)

  (** Fimp filters the generated sublists to keep only those that appear
      frequently (exceeding the threshold least) in the custom vists
      vss. *)
  Definition fimp (vss : list (list A)) (ys : list A) : bool :=
    Nat.leb least ( length ( filter (sublistb eq_dec ys) vss ) ).

  (* Naive program, the spec *)
  Definition fim (vss: list (list A)) (os: list A) : list(list A) :=
    filter (fimp vss) (subs os).

  (** Optimization: Use program calculation to reduce search space. *)

  (* Fusion *)
  Fixpoint fim1 (vss: list(list A))  (os : list A) : list(list A) :=
    match os with
    | [ ] => if (Nat.leb least (length vss) ) then [[]] else []
    | o::os => (fim1 vss os)
                ++ (map (cons o) (fim1 (filter (mem eq_dec o) vss) os))
    end.

  Lemma eq_3 :
    forall vss o l,
      fimp vss (o :: l)  = (fimp (filter (mem eq_dec o) vss)) l.
  Proof.
    induction l; simpl.
    + unfold fimp. simpl.
      pose filter_func_prop as ffp.
      rewrite ffp.
      repeat f_equal.
    + unfold fimp in *.
      pose filter_pipeline_prop as fpp.
      unfold compose in fpp. simpl.
      rewrite <- fpp. trivial.
  Qed.

  Lemma fim1_transformation:
    forall (os : list A) (vss : list (list A)),
      fim vss os = fim1 vss os.
  Proof.
    intros os vss. generalize dependent vss.
    induction os as [ | o os IH ]; intros vss.
    - unfold fim, subs, filter, fimp, sublistb.
      rewrite filter_func_prop.
      simpl. reflexivity.
    - unfold fim in *. simpl.
      rewrite filter_app, <- IH.
      repeat f_equal.
      pose filter_map_prop as fmp.
      pose eq_3 as eq.
      unfold compose, f_eq  in *.
      rewrite fmp. f_equal. rewrite <- IH.
      apply filter_ext.  intro l; apply eq.
  Qed.

  Fixpoint fim2 (vss: list(list A)) r (os : list A) : list(list A) :=
    match os with
    | [ ] => if (Nat.leb (least)(length vss)) then [r] else []
    | o::os => (fim2 vss r os)
                ++ (fim2 (filter (mem eq_dec o) vss) (r ++ [o]) os)
    end.

  Lemma gen_opt:
    forall (os : list A) (vss : list (list A)) r,
      fim2 vss r os = map (app r) (fim vss os).
  Proof.
    induction os; intros.
    - simpl. destruct (least <=? length vss) eqn:H.
      unfold fim. simpl. destruct (fimp vss  []) eqn:H'.
      + simpl. rewrite app_nil_r. reflexivity.
      + simpl in *. unfold fimp in H'. simpl in H'.
        rewrite filter_true in H'. rewrite H in H'.
        discriminate. intros. trivial.
      + unfold fim. simpl. destruct (fimp vss  []) eqn:H'.
        * simpl. rewrite app_nil_r.  simpl in *.
          unfold fimp in H'. simpl in H'. rewrite filter_true in H'. rewrite H in H'.
          discriminate. intros. trivial.
        * simpl. reflexivity.
    - simpl; repeat rewrite IHos.
      set(f:=app r). set(g:=app [a]).
      rewrite map_ext with (f:=app (f [a]))(g:=fun x=>f(g x)).
      + rewrite <- map_map with (f:=g).
        rewrite <- map_app.
        f_equal.
        repeat rewrite fim1_transformation.
        simpl.
        f_equal.
      + intros; unfold f,g ; simpl.
        rewrite <- app_assoc. trivial.
  Qed.

  (** fim2 after base-case filtering applied *)
  Fixpoint fim3 (vss : list (list A)) r (os: list A) : list(list A) :=
    match os with
    | [ ] => [r]
    | o::os => fim3 vss r os ++
                   if Nat.leb least (length(filter (mem eq_dec o) vss))
                   then fim3 (filter (mem eq_dec o) vss) (r ++[o]) os
                   else [ ]
    end.

  Lemma base_trans_false:
    forall (os : list A) (vss : list (list A)) r,
      (Nat.leb (least)(length vss)) = false ->
      fim2 vss r os = [].
  Proof.
    induction os as [ | o os IH ]; simpl;  intros vss r H.
    - destruct (least <=? length vss) eqn : llv.
      + discriminate.
      + trivial.
    - rewrite IH by apply H.
      simpl.
      apply IH.
      assert (length (filter (mem eq_dec o) vss) <= length vss ) as lfv
          by apply  filter_length.
      apply Nat.leb_nle. apply Nat.leb_nle in H. omega.
  Qed.

  (** Lemma that fim2 is equalivent to fim3 when applied to a list of Z **)
  Lemma base_trans_true:
    forall (os : list A) (vss : list (list A)) r,
      (Nat.leb (least)(length vss)) = true ->
      fim2 vss r os = fim3 vss r os.
  Proof.
    induction os as [ | o os IH ]; simpl;  intros vss r H.
    - destruct (least <=? length vss) eqn : llv.
      + trivial.
      + discriminate.
    - rewrite IH by trivial.
      f_equal.
      destruct ( least <=? length (filter (mem eq_dec o) vss) ) eqn:lmv.
      + now apply IH.
      + now apply base_trans_false.
  Qed.

  Lemma fim2_if_fim3_eq:
    forall os vss r,
      fim2 vss r os =
      (if (least <=? length vss) then fim3 vss r os else []).
  Proof.
    induction os as [ | o os IH ]; simpl; intros vss r.
    - trivial.
    - repeat rewrite IH with (vss := filter _ _).
      destruct (least <=? length vss) eqn:Hleast.
      + destruct (least <=? length (filter (mem eq_dec o) vss)) eqn:Hleast'.
        * now repeat rewrite base_trans_true by trivial.
        * repeat rewrite app_nil_r.
          now apply base_trans_true.
      + rewrite <- IH.
        assert (least <=? length (filter (mem eq_dec o) vss) = false) as H.
        {
          apply Nat.leb_nle. apply Nat.leb_nle in Hleast.
          assert ( length (filter (mem eq_dec o) vss) <= length vss)
            by apply filter_length.
          omega.
        }
        now repeat rewrite base_trans_false by trivial.
  Qed.

  Section Vss.

    Parameter Vss : list(list A).

    Notation "'Inv' t" := (Tree.Inv least Vss t) (at level 70).

    (** Binding specific instances of Nodes to proof of invariants *)
    (** Node that is a leaf *)

    Definition size (t: Tree.tree | Inv t) := Tree.size_tree (proj1_sig t) .

    (** Adhoc Predicate needed for trees *)
    Definition lt (t1 t2 : {t:Tree.tree | Inv t}): Prop :=
      (size t1) < (size t2).

    Lemma well_founded_tree_induction :
      well_founded lt.
    Proof.
      unfold lt; intros.
      apply wf_inverse_image with (f:=size).
      apply lt_wf.
    Qed.

    Lemma lt_pi:
      forall t' (a : {t : Tree.tree | Inv t}) (H2 H3 : lt a t'), H2 = H3.
    Proof.
      unfold lt; intros t' a H2 H3; unfold Peano.lt in *.
      apply le_uniqueness_proof.
    Qed.

    Definition embed_Inv (t:Tree.tree|Inv t) :=
      Sig.map (Tree.children (proj1_sig t)) (Tree.Inv_children  (proj2_sig t)).

    Lemma lt_children_Inv:
      forall (t:Tree.tree|Inv t), forall t', List.In t' (embed_Inv t) -> lt t' t.
    Proof.
      intros [ [ r_vss ts] Ht] [t' Ht'] HIn; unfold lt, size.
      unfold embed_Inv, children in HIn. simpl in *.
      apply Sig.in_map_in in HIn; simpl in HIn.
      apply in_split in HIn; destruct HIn as [ ts1 [ts2 Hts ] ]; subst.
      rewrite map_app, fold_left_app, fold_symmetric
        by auto with arith; simpl.
      omega.
    Qed.

    (** Tabulation functions *)
    (** No-recursive version of tab *)
    Definition tab_F tab os (t:{ a : Tree.tree | Inv a }) : list (list A) :=
      match t with
      | exist _ (Tree.Node (r,vss) ts) H =>
        fim3 vss r os ++ flat_map (tab os) (Sig.map ts (Tree.Inv_children  H))
      end.

    Definition twp os t :=
      { t': {ti: {t : Tree.tree | Inv t}| lt ti t} &
            {v : list (list A) &
                 { p : nat |
                   forall k : nat,
                     p < k ->
                     forall g : list A -> {a : Tree.tree | Inv a} -> list (list A),
                       iter k tab_F g os (proj1_sig t') = v} } }.

    Definition embed_termination os
               (t:Tree.tree|Inv t) H (t':{ti:Tree.tree|Inv ti}|lt t' t) :=
      match t' return twp os t with
        exist _ t Ht => existT _ (exist _ t Ht) (H t Ht)
      end.

    Definition get_result os t (t': twp os t): list(list A) :=
      projT1(projT2 t').

    Definition get_iteration os t (t': twp os t) : nat :=
      proj1_sig(projT2(projT2 t')).

    (** tab_terminates : A defintion that proves that given a number of
      interations th   e tab_F function terminates *)
    Definition tab_terminates :
      forall os t,
        {v : list(list A)
             & { p:nat |
                 forall k:nat, p < k ->
                               forall g: list A -> { a : Tree.tree | Inv a } -> list (list A),
                                 iter k tab_F g os t = v } }.
    Proof.
      intros os t.
      induction t using (well_founded_induction well_founded_tree_induction).
      set(term:= embed_termination os H).
      set(l := map_sig term (Sig.map (embed_Inv t) (lt_children_Inv t))).
      set(results    := map (@get_result os t) l).
      set(iterations := map (@get_iteration os t) l).
      set(t_backup:=t).
      destruct t as [[[r vss] ts] Ht].
      exists (fim3 vss r os ++ flat_map (fun x=>x) results).
      exists (2 + fold_left Nat.max iterations 0).
      intros k Hk g.
      destruct k as [ | k' ].
      - omega.
      - assert(forall pos, get_iteration (Sig.nth l pos) < k') as Hiter.
        {
          intros pos; set(value := Sig.nth l pos).
          assert(List.In (get_iteration value) iterations).
          {
            unfold iterations, value, l ; apply in_map.
            apply Sig.nth_In.
          }
          eapply Nat.lt_trans.
          - apply le_lt_n_Sm.
            eapply max_In; eauto.
          - auto with arith.
        }
        assert(length l = length (embed_Inv t_backup)) as Hlen.
        {
          unfold l, embed_Inv, t_backup, children.
          now autorewrite with length.
        }
        assert(forall pos,
                  get_result (Sig.nth l pos) =
                  iter k' tab_F g os
                       (Sig.nth (embed_Inv t_backup)
                                (Sig.cast_sig pos (Sig.length_sig Hlen)))).
        {
          intros pos; set(value := Sig.nth l pos).
          assert(List.In (get_result value) results).
          {
            unfold results, value ; apply in_map.
            apply Sig.nth_In.
          }
          unfold get_result, value.
          set(property:=projT2(projT2(Sig.nth l pos))); simpl in property.
          set(count:=proj1_sig property).
          set(Hcount:=proj2_sig property); simpl in Hcount.
          rewrite <- Hcount with (k:= k')(g:=g).
          - f_equal; unfold l.
            rewrite sig_nth_map_sig.
            rewrite Sig.map_nth by apply lt_pi.
            unfold term; simpl.
            erewrite Sig.nth_pi.
            + reflexivity.
            + now repeat rewrite proj1_sig_cast_sig.
          - unfold term in Hiter.
            unfold property.
            apply Hiter.
        }
        simpl; f_equal.
        repeat rewrite flat_map_concat_map.
        rewrite map_id; f_equal.
        eapply Sig.nth_eq.
        intro pos; unfold results.
        repeat rewrite Sig.nth_map.
        rewrite H0; f_equal.
        apply Sig.nth_pi.
        now repeat rewrite proj1_sig_cast_sig.
        Unshelve.
        symmetry; unfold results, l, embed_Inv, term,
                  embed_termination, children; simpl.
        now repeat (autorewrite with length;
                    try rewrite map_sig_length with (f:=term)).
    Defined.

    (** Tab function that returns the result of tab_terminates *)
    Definition tab os t : list (list A) :=
      projT1 (tab_terminates os t).

    (** Proof of the fixpoint equation *)
    Theorem tab_equation :
      forall os t,
        tab os t = tab_F tab os t.
    Proof.
      intros os t.
      induction t using (well_founded_induction well_founded_tree_induction).
      pose(backup:=t).
      pose(t_children:=Tree.children (` t)).
      pose(l := map_sig (fun t => existT _ t (tab_terminates os t))
                        (Sig.map t_children (Tree.Inv_children  (proj2_sig t)))).
      pose(iterations := map (fun t=>proj1_sig(projT2(projT2 t))) l).
      pose(results := map (fun t=>projT1(projT2 t)) l).
      unfold tab at 1.
      destruct(tab_terminates os t) as [ result [iteration Hresult] ].
      pose(p:=S(S(Nat.max (fold_left Nat.max iterations 0) iteration))).
      destruct t as [[[r vss] ts] Ht]; simpl.
      rewrite <- Hresult with (g:=tab)(k:=p); unfold p; simpl.
      f_equal.
      apply flat_map_assumption.
      - intros t HIn.
        unfold tab at 2.
        pose(result_t:=projT1(tab_terminates os t)).
        pose(iteration_t:=proj1_sig(projT2(tab_terminates os t))).
        pose(Hresult_t:=proj2_sig(projT2(tab_terminates os t))).
        simpl in *.
        rewrite <- Hresult_t with
            (g:=tab)(k:=S(Nat.max (fold_left Nat.max iterations 0) iteration)).
        + reflexivity.
        + pose(f:=fun x=>` (projT2 (tab_terminates os x))).
          assert(List.In (f t) iterations) as Hiter_In.
          {
            unfold iterations, l, t_children; simpl.
            rewrite map_map_sig. unfold compose; simpl.
            now apply in_map.
          }
          replace (f t) with (iteration_t) in Hiter_In by auto.
          unfold iteration_t in *.
          apply max_In in Hiter_In.
          zify; omega.
      - zify; omega.
    Qed.

    Lemma tab_pi:
      forall t t' os , proj1_sig t = proj1_sig t' -> tab os t = tab os t'.
    Proof.
      intros [t Ht].
      induction t as [ r vss ts IH ] using Tree.tree_induction.
      intros [[[r' vss'] ts'] Ht'] os Heq; simpl in *.
      inversion Heq; subst.
      repeat rewrite tab_equation. simpl.
      f_equal.
      assert(List.map (@proj1_sig _ _) (Sig.map ts' (Tree.Inv_children  Ht)) = ts')
        by (now  rewrite Sig.map_proj1_sig).
      assert(List.map (@proj1_sig _ _) (Sig.map ts' (Tree.Inv_children  Ht')) = ts')
        by (now  rewrite Sig.map_proj1_sig).
      generalize dependent (Sig.map ts' (Tree.Inv_children  Ht)).
      generalize dependent (Sig.map ts' (Tree.Inv_children  Ht')).
      clear Ht Ht'.
      induction ts' as [ | t' ts' IHts' ];
        intros [ | x xs ] Hxs [ | y ys] Hys;
        rewrite <- Hxs in Hys; trivial.
      - simpl in *; inversion Hys.
      - simpl in *; inversion Hys.
      - simpl in *; inversion Hxs.
      - simpl in *; inversion Hxs.
      - simpl in *; inversion Hys.
      - simpl in *. f_equal.
        + inversion Hys; inversion Hxs; subst.
          destruct y as [y Hy ]. destruct x as [ x Hx ]; apply IH; auto.
        + apply IHts'; auto.
          * now inversion Hxs.
          * rewrite Hxs in Hys; now inversion Hys.
    Qed.

    Lemma flat_map_tab_pi:
      forall ts os H1 H2,
        flat_map (tab os)(Sig.map ts H1) =
        flat_map (tab os)(Sig.map ts H2).
    Proof.
      induction ts as [ | t ts IH ]; trivial.
      intros os H1 H2; simpl.
      f_equal.
      - now apply tab_pi.
      - apply IH.
    Qed.

    (** Tabulation Properties *)

    Lemma eq_8:
      forall os r vss H1 H2, fim3 vss r os =
                        tab os (@Leaf least Vss r vss H1 H2).
    Proof.
      induction os; simpl; intros; rewrite tab_equation.
      - trivial.
      - simpl; now rewrite app_nil_r.
    Qed.

    Lemma eq_9:
      forall t o os ,
        (forall r vss, Tree.NodeIn (r,vss) (proj1_sig t) ->
                  ((length (filter (mem A.eq_dec o) vss)) <? least) = true) ->
        tab (o :: os) t = tab os t.
    Proof.
      intros [t H]; pose(Hleast:= Inv_at_least H).
      induction t as [ r vss ts Hts ] using tree_induction;
        intros o os H0 ; simpl;
          rewrite tab_equation;  simpl; rewrite associative; f_equal.
      rewrite <- fim2_if_fim3_eq.
      assert (fim2 (filter (mem A.eq_dec o) vss) (r ++ [o]) os = [] )
        as fime.
      {
        apply base_trans_false.
        assert ( NodeIn (r, vss) (Node (r, vss) ts) ) as Hin by constructor.
        specialize (H0 r vss Hin). rewrite Nat.leb_antisym.
        rewrite H0. trivial.
      }
      rewrite fime. rewrite tab_equation; simpl.
      f_equal.
      destruct(least <=? length (filter (mem A.eq_dec o) vss)); simpl;
        apply flat_map_assumption;
        (intros [a Ha] Hin; apply Sig.in_map_in in Hin; apply Hts;
         [ assumption | intros; eapply H0; constructor;
                        apply Exists_exists; exists a;eauto]).
    Qed.

    (** Select : selects the frequent sets from the tabulation tree (t) *)
    Fixpoint select tree :=
      match tree with
      | Node (r,vss) ts => [r] ++ flat_map (select ) ts
      end.

    Fixpoint tab' os t : list (list A) :=
      match os with
      | [ ] => select t
      | o :: os => tab' os  (add least o t)
      end.

    Lemma Inv_lt_least:
      forall o t, Inv t -> length(filter (mem A.eq_dec o) (vss_of t)) < least ->
             forall r vss, NodeIn (r, vss) t ->
                      length(filter (mem A.eq_dec o) vss) < least.
    Proof.
      intros o t HInv Hleast r vss HIn.
      apply NodeIn_In in HIn. destruct HIn as [ ts Hts ].
      assert(vss_of t = filter (sublistb A.eq_dec (root_of t)) Vss) as HH
          by (apply HInv; rewrite (tree_split t); constructor).
      rewrite HH in *; clear HH.
      assert(vss = filter (sublistb A.eq_dec r) Vss) as HH
          by (apply (Inv_In HInv Hts); constructor).
      rewrite HH; clear HH.
      assert(sublist (o::(root_of t)) (o::r)).
      {
        simpl; split; [ idtac | now left ].
        apply sublist_dec with (eq_dec:=A.eq_dec).
        apply sublistb_cons_r, sublist_dec.
        destruct t as [ [r0 vss0] ts0]; inversion Hts; subst.
        - simpl; apply sublist_dec with (eq_dec:=A.eq_dec), sublistb_refl.
        - assert(Sub (Node(r,vss)ts)(Node(r0,vss0)ts0)) as HH
              by(eapply In_Sub_trans; eauto; econstructor; eauto).
          destruct HInv as [HI1 HI2 HI3].
          specialize (HI3 _ _ HH (_root _)); simpl in *.
          apply HI3.
      }
      match goal with
      | [ H: ?e < _ |- _ ] => apply le_lt_trans with (m:=e); auto
      end.
      replace (mem A.eq_dec o) with (sublistb A.eq_dec [o]) by auto.
      repeat rewrite filter_pipeline_prop.
      repeat
        match goal with
        | [ |- context [ length (filter (fun x=>sublistb ?eq ?l1 x &&
                                                     sublistb ?eq ?l2 x) ?arg) ] ] =>
          replace (filter(fun x=>sublistb eq l1 x && sublistb eq l2 x) arg)
            with  (filter(sublistb eq (l1++l2)) arg)
            by (apply filter_ext; intro x; apply sublistb_app)
        end.
      now apply filter_sublistb_length.
    Qed.

    Lemma tab_tab':
      forall os (t:tree | Inv t),
        tab os t = tab' os (proj1_sig t).
    Proof.
      induction os as [ | o os IHos ];
        intros [t HInv];
        induction t as [r vss ts IH ] using tree_induction; simpl in IH.
      - rewrite tab_equation;  simpl.
        destruct HInv as [H1 H2 H3].
        destruct(least <=? length vss) eqn:Hleast_b.
        + simpl in *; f_equal; symmetry.
          erewrite <- Sig.map_proj1_sig with (l:=ts) at 1.
          rewrite flat_map_concat_map, map_map, <- flat_map_concat_map.
          apply flat_map_assumption; intros t Hin_t.
          destruct t as [t Ht ]. apply Sig.in_map_in in Hin_t; simpl in *.
          replace (select t) with (tab' [] t) by auto.
          now erewrite IH by eauto.
        + apply Nat.leb_nle in Hleast_b.
          assert(least<= length vss) by (eapply H1; constructor).
          contradiction.
      - rewrite tab_equation. simpl tab_F. (* eq. (5) *)
        pose(Hleast:=Inv_at_least HInv).
        (* We need to destruct, so the various steps in the paper
           are distributed among the two cases *)
        destruct(least <=? length (filter (mem A.eq_dec o) vss)) eqn:Hleast'.
        + apply leb_complete in Hleast'.
          assert(filter (mem A.eq_dec o) vss =
                 filter (sublistb A.eq_dec (r ++ [o])) Vss) as Hfilter.
          {
            destruct HInv as [H1 H2 H3].
            assert(HH: vss = filter (sublistb A.eq_dec r) Vss)
              by (apply H2; constructor).
            rewrite HH; clear HH.
            rewrite filter_pipeline_prop.
            apply filter_ext; intro l.
            rewrite sublistb_app; simpl.
            apply andb_comm.
          }
          erewrite eq_8 with (H1:=Hfilter)(H2:=Hleast'). (* eq. (8) *)
          rewrite flat_map_assumption
            with (g:=(tab' os) ∘ ((add least o) ∘ (@proj1_sig _ _)))
            by (intros [a Ha] HIn; autounfold;
                rewrite IH by (now apply Sig.in_map_in in HIn);
                simpl; auto). (* eq. (11) *)
          rewrite flat_map_map; autounfold;
            rewrite <- map_map, Sig.map_proj1_sig; simpl proj1_sig;
              rewrite  <- List.app_assoc. (* eq. (6) *)
          rewrite IHos; simpl proj1_sig.
          replace (tab' os
                        (Node (r ++ [o], filter (mem A.eq_dec o) vss) []) ++
                        flat_map (tab' os) (map (add least o) ts))
            with (flat_map (tab' os)
                           ([(Node (r ++ [o], filter(mem A.eq_dec o) vss)[])]
                              ++(map (add least o) ts))) by auto. (*eq. (7)*)
          pose(t_new := Node(r,vss)
                            ([Node (r ++ [o], filter(mem A.eq_dec o)vss) []]
                               ++map (add least o) ts)).
          assert(Inv t_new) as Ht_new.
          {
            eapply new_o_Inv; auto.
            - intros. eapply add_Inv, Inv_children; eauto.
            - now apply Nat.leb_le.
          }
          assert(forall t, List.In t
                              ([Node (r ++ [o], filter (mem A.eq_dec o) vss) []]
                                 ++ map (add least o) ts) -> Inv t) as HIt
              by apply (Inv_children  Ht_new).
          rewrite <- Sig.map_proj1_sig with (H:=HIt).
          rewrite <- flat_map_map.
          rewrite flat_map_assumption with (g:=tab os).
          * pose (HTE:=tab_equation). unfold tab_F in HTE.
            specialize (HTE os (exist _ t_new Ht_new)).
            Opaque app. simpl in HTE.
            erewrite flat_map_tab_pi in HTE.
            simpl. apply leb_correct in Hleast'; rewrite Hleast'.
            unfold t_new. rewrite <- HTE.
            now rewrite  IHos; unfold t_new; simpl.
          * intros; now rewrite IHos.
        + rewrite flat_map_assumption with (g:=tab os)
            by (intros a Ha; apply eq_9; intros r0 vss0 H0; apply leb_correct;
                apply Nat.leb_nle, Nat.nle_gt in Hleast';
                eapply Inv_lt_least with (r:=r0); repeat (simpl;  eauto);
                constructor; apply Exists_exists; eexists; split; eauto;
                erewrite <- Sig.map_proj1_sig; apply in_map; eauto). (*eq.(9)*)
          rewrite app_nil_r; simpl proj1_sig.
          pose (HTE:=tab_equation). unfold tab_F in HTE.
          specialize (HTE os (exist _ (Node(r,vss)ts) HInv)).
          rewrite <- HTE. simpl.  rewrite Hleast'.
          apply IHos.
    Qed.

    Definition fim4 (vss:list(list A)) (os:list A): list(list A) :=
      if least <=? length vss then tab' os (Node ([],vss) []) else [].

    Instance fim_fim1: Opt (fim Vss) (fim1 Vss).
    Proof.
      constructor; intros os.
      now apply fim1_transformation.
    Qed.

    Instance fim1_fim2: Opt (fim1 Vss) (fim2 Vss []).
    Proof.
      constructor; intros os.
      rewrite gen_opt.
      rewrite map_ext with (g:=fun l:list A=>l) by auto.
      rewrite map_id.
      symmetry. apply opt_eq.
    Qed.

    Definition at_least (vss res:list(list A)) : list(list A) :=
      if least <=? length vss
      then res
      else [].

    Instance fim2_fim3 r:
      Opt (fim2 Vss r) ((at_least Vss) ∘ (fim3 Vss r)).
    Proof.
      constructor; intro os.
      apply fim2_if_fim3_eq.
    Qed.

    Instance fim3_fim4:
      Opt((at_least Vss) ∘ (fim3 Vss []))
         (fim4 Vss).
    Proof.
      constructor; intro.
      unfold at_least, compose, fim4.
      destruct( least <=? length Vss) eqn:Hleast.
      - assert(H1: Vss = filter (sublistb A.eq_dec []) Vss)
          by now rewrite filter_true.
        assert(H2: least <= length Vss)
          by now apply Nat.leb_le.
        erewrite eq_8 with(H1:=H1)(H2:=H2).
        now apply tab_tab'.
      - trivial.
    Qed.

    Theorem fim4_fim:
      forall os, fim4 Vss os = fim Vss os.
    Proof.
      intro os. symmetry.
      repeat (etransitivity; [idtac | apply opt_eq]).
      reflexivity.
    Qed.

  End Vss.

End FimLeast.
End FIM.

Module Fim (Import A: HasEqDec). Include FIM A. End Fim.

(** FimOrder : Version where Vss is ordered *)
Module FimOrder
       (Import A: HasEqDec)
       (Import AOrder : AOrder A)
       (Import ListOrder: ListOrder A AOrder).

  Module Import Fim := Fim A.
  Import ListOrder A AOrder.

  Section LeastVss.

    Variable  least : nat.
    Variable  Vss : list (list A).

    Notation "'Inv' t" := (Tree.Inv least Vss t) (at level 70).

    (** Optimization where lists in vss are assumed to be ordered. **)
    Fixpoint add' o t : Fim.Tree.tree :=
      match t with
      | Fim.Tree.Node (r,vss) ts =>
        let o_vss := filter (ListOrder.isElement o) vss in
        if Nat.leb least (length o_vss)
        then Fim.Tree.Node (r,vss) (([Fim.Tree.Node (r++[o], o_vss) []]
                              ++ map (add' o) ts))
        else t
      end.

    Lemma Inv_is_sorted:
      forall t, (forall l, List.In l Vss -> ListOrder.is_sorted l = true) -> Inv t ->
           forall t', Tree.In t' t ->
                 forall l, List.In l (Tree.vss_of t') -> ListOrder.is_sorted l = true.
    Proof.
      intros t H HInv t' H1 l H2.
      destruct HInv as [ HInv1 HInv2 HInv3 ].
      unfold Tree.I1, Tree.I2, Tree.I3 in *.
      assert(HIn: Tree.NodeIn(Tree.root_of t', Tree.vss_of t') t).
      {
        apply Tree.NodeIn_In.
        exists(Tree.children t').
        now rewrite <- Tree.tree_split.
      }
      assert(Hvss: Tree.vss_of t' =
                   filter(List.sublistb A.eq_dec (Tree.root_of t')) Vss)
        by now apply HInv2.
      rewrite Hvss in H2.
      apply filter_In in H2.
      now apply H.
    Qed.

    Lemma add_add'_Inv_is_sorted:
      forall t o, Inv t ->
             (forall l, List.In l Vss -> is_sorted l = true) ->
            Tree.add least o t = add' o t.
    Proof.
      induction t as [ r vss ts IH ] using Tree.tree_induction.
      intros o HInv H; simpl.
      assert(HH:filter (mem A.eq_dec o) vss =
                  filter (ListOrder.isElement o) vss).
      {
        apply Fim.List.filter_assumption.
        intros l HIn; apply mem_isElement, H.
        assert(Heq: vss = filter(Fim.List.sublistb A.eq_dec r) Vss)
          by (apply HInv; now constructor).
        rewrite Heq in HIn.
        now apply filter_In in HIn.
      }
      destruct(least <=? length (filter (mem A.eq_dec o) vss)) eqn:Hleast'.
      - rewrite HH in *. rewrite Hleast'.
        do 2 f_equal.
        apply map_assumption.
        intros x HIn.
        apply IH; auto.
        eapply Tree.Inv_children; eauto.
      - rewrite HH in *. now rewrite Hleast'.

    Qed.

    Fixpoint tab'' os t : list (list A) :=
      match os with
      | [ ] => select t
      | o :: os => tab'' os  (add' o t)
      end.

    Lemma tab'_tab''_Inv_is_sorted:
      forall os t, Inv t ->
              (forall l, List.In l Vss -> is_sorted l = true) ->
              tab' least os t = tab'' os t.
    Proof.
      induction os as [ | o os IH]; intros t HInv H.
      - reflexivity.
      - simpl. rewrite IH by (auto; apply Tree.add_Inv;auto).
        f_equal. now apply add_add'_Inv_is_sorted.
    Qed.

    Ltac to_prop :=
      match goal with
      | [  H: Nat.leb _ _ = true |- _ ] =>
        apply Nat.leb_le in H
      | [  H: Nat.leb _ _ = false |- _ ] =>
        apply Nat.leb_nle in H; apply Nat.nle_gt in H
      end.

    Definition fim5 (vss:list(list A))(os:list A) : list(list A) :=
      if least <=? length vss then tab'' os (Tree.Node ([],vss) []) else [].

    Instance fim4_fim5 (H:forall l, List.In l Vss -> is_sorted l = true) :
      Opt (fim4 least Vss) (fim5 Vss).
    Proof.
      unfold fim4, fim5; constructor; intros os.
      simpl; destruct(least <=? length Vss) eqn:Hleast.
      - rewrite tab'_tab''_Inv_is_sorted
          by (auto; apply Tree.Inv_empty; now to_prop).
        reflexivity.
      - trivial.
    Qed.
  End LeastVss.
End FimOrder.

Close Scope sydpacc_scope.
