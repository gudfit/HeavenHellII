From Stdlib Require Import List Lia Arith PeanoNat Bool.
From HH.rinclude Require Import RulesHeavenHell.

Set Implicit Arguments.

Module ScaleLaw.

  Module UniformHub_NoTau.
    Section S.
      Import HeavenHell.

      Variable V : Type.
      Variable dec : forall x y:V, {x=y}+{x<>y}.
      Variable allV : list V.
      Hypothesis allV_nodup : NoDup allV.
      Hypothesis allV_complete : forall v:V, In v allV.
      Variable w : V -> V -> nat.
      Variable g : V.
      Variable W : nat.
      Hypothesis hub_uniform : forall v, v <> g -> @hub_weight V w g v = W.

      Theorem one_step_all_glory_iff_W_ge_max_rest :
        (forall s v, @next_heaven V dec allV w g s v = Glory)
        <-> W >= @max_rest V dec allV w g.
      Proof.
        exact (@uniform_hub_one_step_iff V dec allV allV_nodup allV_complete w g W hub_uniform).
      Qed.

      Theorem one_step_all_glory_if_W_ge_degmax :
        W >= @indeg_global V dec allV w g * @wmax_global V dec allV w g ->
        (forall s v, @next_heaven V dec allV w g s v = Glory).
      Proof.
        intro HW.
        eapply (@uniform_hub_one_step_sufficient_degmax V dec allV allV_nodup allV_complete w g).
        - exact hub_uniform.
        - exact HW.
      Qed.

    End S.
  End UniformHub_NoTau.

  Module UniformHub_WithTau.
    Section S.
      Import HeavenHell.

      Variable V : Type.
      Variable dec : forall x y:V, {x=y}+{x<>y}.
      Variable allV : list V.
      Hypothesis allV_nodup : NoDup allV.
      Hypothesis allV_complete : forall v:V, In v allV.
      Variable w : V -> V -> nat.
      Variable g : V.
      Variable tau : V -> nat.
      Variable W : nat.
      Hypothesis hub_uniform : forall v, v <> g -> @hub_weight V w g v = W.

      Theorem one_step_all_glory_iff_W_ge_max_need_tau :
        (forall s v, @next_heaven_tau V dec allV w g tau s v = Glory)
        <-> W >= @max_need_tau V dec allV w g tau.
      Proof.
        exact (@uniform_hub_tau_one_step_iff V dec allV allV_nodup allV_complete w g W hub_uniform tau).
      Qed.

      Theorem one_step_all_glory_if_W_ge_max_need_tau_degmax :
        W >= @max_need_tau_degmax V dec allV w g tau ->
        (forall s v, @next_heaven_tau V dec allV w g tau s v = Glory).
      Proof.
        intro HW.
        eapply (@uniform_hub_tau_one_step_sufficient_degmax V dec allV allV_nodup allV_complete w g tau).
        - intros v Hv. apply hub_uniform; exact Hv.
        - exact HW.
      Qed.

      Theorem nonuniform_pointwise_sufficient:
        (forall v, v <> g -> @hub_weight V w g v + tau v >= @rest_weight V dec allV w g v)
        -> (forall s v, @next_heaven_tau V dec allV w g tau s v = Glory).
      Proof.
        intro Hpt.
        apply (proj2 (@heaven_one_step_all_G_iff_domination_ge_tau V dec allV allV_nodup allV_complete w g tau)).
        intros v Hv; apply Hpt; exact Hv.
      Qed.

      Definition set := V -> bool.
      Definition sum_from (H:set) (v:V) : nat :=
        @sum_all V allV (fun u => if H u then w u v else 0).
      Definition outside_sum (H:set) (v:V) : nat :=
        @sum_all V allV (fun u => if dec u g then 0 else if H u then 0 else w u v).

      Lemma sum_from_split_hub:
        forall (H:set) v, H g = true ->
        sum_from H v = @hub_weight V w g v + @w_from V dec allV w g H v.
      Proof.
        intros H v Hg.
        unfold sum_from, hub_weight, w_from.
        set (f1 := fun u => if dec u g then w u v else 0).
        set (f2 := fun u => if dec u g then 0 else if H u then w u v else 0).
        transitivity (@sum_all V allV (fun u => f1 u + f2 u)).
        - apply (@sum_all_ext V allV). intros u _.
          unfold f1, f2.
          destruct (dec u g) as [->|Hug].
          + rewrite Hg. cbn. lia.
          + cbn. destruct (H u); reflexivity.
        - rewrite (@sum_all_add V allV f1 f2).
          change (@sum_all V allV f1) with (@sum_all V allV (fun u => if dec u g then w u v else 0)).
          change (@sum_all V allV f2) with (@sum_all V allV (fun u => if dec u g then 0 else if H u then w u v else 0)).
          set (k := fun u => w u v).
          change (@sum_all V allV (fun u => if dec u g then w u v else 0))
            with (@sum_all V allV (fun u => if dec u g then k u else 0)).
          rewrite (@sum_all_mask_g V dec allV allV_nodup allV_complete g k).
          reflexivity.
      Qed.

      Theorem multi_hub_seeded_one_step:
        forall (H:set), H g = true ->
        (forall v, v <> g -> sum_from H v + tau v >= outside_sum H v) ->
        forall s v, v <> g -> @next_heaven_tau V dec allV w g tau (@seed_state V H s) v = Glory.
      Proof.
        intros H Hg HDom s v Hv.
        pose (S := H).
        specialize (HDom v Hv).
        rewrite (sum_from_split_hub H v Hg) in HDom.
        replace (outside_sum H v) with (@rest_outside V dec allV w g H v) in HDom by reflexivity.
        eapply (@two_step_sufficient_tau V dec allV allV_nodup allV_complete w g tau); [exact Hv|exact HDom].
      Qed.

      Theorem inbound_budget_sufficient:
        forall K,
          (forall v, v <> g -> @rest_weight V dec allV w g v <= K) ->
          W >= K ->
          (forall s v, @next_heaven_tau V dec allV w g tau s v = Glory).
      Proof.
        intros K Hcap HW.
        eapply (proj2 (@heaven_one_step_all_G_iff_domination_ge_tau V dec allV allV_nodup allV_complete w g tau)).
        intros v Hv.
        specialize (Hcap v Hv). rewrite hub_uniform by exact Hv.
        eapply Nat.le_trans; [apply Hcap|]. lia.
      Qed.

    End S.
  End UniformHub_WithTau.

  Module MultiHub_Forced.
    Section S.
      Import HeavenHell.

      Variable V : Type.
      Variable dec : forall x y:V, {x=y}+{x<>y}.
      Variable allV : list V.
      Hypothesis Hnodup : NoDup allV.
      Hypothesis Hcomplete : forall v:V, In v allV.
      Variable w : V -> V -> nat.

      Definition set := V -> bool.

      Definition force_H (H:set) (s:V->State) : V->State :=
        fun u => if H u then Glory else s u.

      Definition hub_weight_H (H:set) (v:V) : nat :=
        @sum_all V allV (fun u => if H u then w u v else 0).

      Definition rest_weight_H (H:set) (v:V) : nat :=
        @sum_all V allV (fun u => if H u then 0 else w u v).

      Variable tau : V -> nat.

      Definition next_heaven_tau_H (H:set) (s:V->State) (v:V) : State :=
        let s' := force_H H s in
        let SG := @score V allV w s' Glory v in
        let SN := @score V allV w s' Gnash  v in
        if Nat.ltb (SG + tau v) SN then Gnash else Glory.

      Lemma scoreN_le_rest_H :
        forall H s v,
          @score V allV w (force_H H s) Gnash v <= rest_weight_H H v.
      Proof.
        intros H s v.
        unfold rest_weight_H, score, force_H.
        eapply (@sum_all_le V allV).
        intros u _.
        destruct (H u) eqn:Hu; cbn.
        - lia.
        - apply mul_ind_le.
      Qed.

      Lemma scoreG_ge_hub_H :
        forall H s v,
          hub_weight_H H v <= @score V allV w (force_H H s) Glory v.
      Proof.
        intros H s v.
        unfold hub_weight_H, score, force_H.
        eapply (@sum_all_le V allV).
        intros u _.
        destruct (H u) eqn:Hu; cbn.
        - cbn [state_eqb ind]. lia.
        - apply mul_ind_nonneg.
      Qed.

      Definition all_gnash : V -> State := fun _ => Gnash.

      Lemma scoreG_all_gnash_eq_hub_H :
        forall H v,
          @score V allV w (force_H H all_gnash) Glory v = hub_weight_H H v.
      Proof.
        intros H v.
        unfold score, hub_weight_H, force_H, all_gnash.
        eapply (@sum_all_ext V allV).
        intros u _.
        destruct (H u) eqn:Hu; cbn [state_eqb ind]; lia.
      Qed.

      Lemma scoreN_all_gnash_eq_rest_H :
        forall H v,
          @score V allV w (force_H H all_gnash) Gnash v = rest_weight_H H v.
      Proof.
        intros H v.
        unfold score, rest_weight_H, force_H, all_gnash.
        eapply (@sum_all_ext V allV).
        intros u _.
        destruct (H u) eqn:Hu; cbn [state_eqb ind]; lia.
      Qed.

      Lemma domination_tau_H_implies_glory :
        forall H s v,
          rest_weight_H H v <= hub_weight_H H v + tau v ->
          next_heaven_tau_H H s v = Glory.
      Proof.
        intros H s v Hdom.
        unfold next_heaven_tau_H.
        set (s' := force_H H s).
        set (SG := @score V allV w s' Glory v).
        set (SN := @score V allV w s' Gnash  v).
        assert (Hsn : SN <= rest_weight_H H v) by (subst SN s'; apply scoreN_le_rest_H).
        assert (Hhub : hub_weight_H H v <= SG) by (subst SG s'; apply scoreG_ge_hub_H).
        assert (Hle : SN <= SG + tau v).
        { eapply Nat.le_trans; [apply Hsn|]. eapply Nat.le_trans; [apply Hdom|]. lia. }
        destruct (Nat.ltb (SG + tau v) SN) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|reflexivity].
      Qed.

      Theorem one_step_all_G_iff_sumH_dom_tau :
        forall H,
          (forall s v, next_heaven_tau_H H s v = Glory)
          <-> (forall v, hub_weight_H H v + tau v >= rest_weight_H H v).
      Proof.
        intro H; split.
        - intros Hall v.
          specialize (Hall all_gnash v).
          unfold next_heaven_tau_H in Hall.
          set (SG := @score V allV w (force_H H all_gnash) Glory v).
          set (SN := @score V allV w (force_H H all_gnash) Gnash  v).
          rewrite (scoreG_all_gnash_eq_hub_H H v) in Hall.
          rewrite (scoreN_all_gnash_eq_rest_H H v) in Hall.
          destruct (Nat.ltb (hub_weight_H H v + tau v) (rest_weight_H H v)) eqn:Hlt; [discriminate|].
          now apply Nat.ltb_ge in Hlt.
        - intros Hdom s v.
          apply (domination_tau_H_implies_glory H s v).
          apply Hdom.
      Qed.

    End S.
  End MultiHub_Forced.

End ScaleLaw.
 
 Module Monotonicity.
   Section S.
     Import HeavenHell.

     Variable V : Type.
     Variable dec : forall x y:V, {x=y}+{x<>y}.
     Variable allV : list V.
     Hypothesis Hnodup : NoDup allV.
     Hypothesis Hcomplete : forall v:V, In v allV.
     Variable w : V -> V -> nat.
     Variable g : V.

     Variable tau  : V -> nat.
     Variable tau' : V -> nat.

     Lemma tau_monotone :
       (forall v, tau v <= tau' v) ->
       @max_need_tau V dec allV w g tau' <=
       @max_need_tau V dec allV w g tau.
     Proof.
       intro Hle.
       set (W := @max_need_tau V dec allV w g tau).
       change (@max_need_tau V dec allV w g tau' <= W).
       unfold max_need_tau.
       eapply HeavenHell.list_max_le_of_forall.
       intros x Hx.
       apply in_map_iff in Hx as [v [Hxv Hin]]. subst x.
       unfold need_tau.
       eapply Nat.le_trans.
       - apply Nat.sub_le_mono_l. apply Hle.
       - change (rest_weight dec allV w g v - tau v)
           with (@need_tau V dec allV w g tau v).
         apply HeavenHell.in_map_le_list_max. exact Hin.
     Qed.

     Corollary tau_increase_weakens_requirement :
       (forall v, tau v <= tau' v) ->
       forall W,
         W >= @max_need_tau V dec allV w g tau ->
         W >= @max_need_tau V dec allV w g tau'.
     Proof.
       intros Hle W HW.
       eapply Nat.le_trans; [apply (tau_monotone Hle)|exact HW].
     Qed.

     Lemma seed_monotone :
       forall (S1 S2:V->bool) v,
         (forall u, S1 u = true -> S2 u = true) ->
         @rest_outside V dec allV w g S2 v <= @rest_outside V dec allV w g S1 v
         /\ @w_from V dec allV w g S1 v <= @w_from V dec allV w g S2 v.
     Proof.
       intros S1 S2 v Hsub; split.
       - unfold rest_outside.
        eapply (@sum_all_le V allV). intros u _.
         destruct (dec u g) as [|Hg]; cbn; [lia|].
         destruct (S1 u) eqn:HS1; destruct (S2 u) eqn:HS2; cbn.
         + lia.
         + exfalso. specialize (Hsub u). specialize (Hsub HS1). now rewrite HS2 in Hsub.
         + lia.
         + lia.
       - unfold w_from.
         eapply (@sum_all_le V allV). intros u _.
         destruct (dec u g) as [|Hg]; cbn; [lia|].
         destruct (S1 u) eqn:HS1; destruct (S2 u) eqn:HS2; cbn.
         + lia.
         + exfalso. specialize (Hsub u). specialize (Hsub HS1). now rewrite HS2 in Hsub.
         + lia.
         + lia.
     Qed.

     Corollary seed_increase_helps_two_step :
       forall (S1 S2:V->bool) v,
         (forall u, S1 u = true -> S2 u = true) ->
         @hub_weight V w g v + @w_from V dec allV w g S1 v + tau v >= @rest_outside V dec allV w g S1 v ->
         @hub_weight V w g v + @w_from V dec allV w g S2 v + tau v >= @rest_outside V dec allV w g S2 v.
     Proof.
       intros S1 S2 v Hsub H.
       destruct (seed_monotone S1 S2 v Hsub) as [Hrest Hwfrom].
       eapply Nat.le_trans; [apply Hrest|].
       eapply Nat.le_trans; [exact H|].
       assert (Hinc:
         @hub_weight V w g v + @w_from V dec allV w g S1 v + tau v
         <= @hub_weight V w g v + @w_from V dec allV w g S2 v + tau v) by lia.
       exact Hinc.
     Qed.

     Corollary seed_increase_helps_two_step_all :
       forall (S1 S2:V->bool),
         (forall u, S1 u = true -> S2 u = true) ->
         (forall v, v <> g ->
             @hub_weight V w g v + @w_from V dec allV w g S1 v + tau v
             >= @rest_outside V dec allV w g S1 v) ->
         (forall v, v <> g ->
             @hub_weight V w g v + @w_from V dec allV w g S2 v + tau v
             >= @rest_outside V dec allV w g S2 v).
     Proof.
       intros S1 S2 Hsub Hall v Hv.
       specialize (Hall v Hv).
       destruct (seed_monotone S1 S2 v Hsub) as [Hrest Hwfrom].
       eapply Nat.le_trans; [apply Hrest|].
       eapply Nat.le_trans; [exact Hall|].
       assert (Hinc:
         @hub_weight V w g v + @w_from V dec allV w g S1 v + tau v
         <= @hub_weight V w g v + @w_from V dec allV w g S2 v + tau v) by lia.
       exact Hinc.
     Qed.

     Corollary seed_increase_helps_two_step_all_uniform :
       forall (S1 S2:V->bool) (W:nat),
         (forall u, S1 u = true -> S2 u = true) ->
         (forall v, v <> g -> @hub_weight V w g v = W) ->
         (forall v, v <> g -> W + @w_from V dec allV w g S1 v + tau v >= @rest_outside V dec allV w g S1 v) ->
         (forall v, v <> g -> W + @w_from V dec allV w g S2 v + tau v >= @rest_outside V dec allV w g S2 v).
     Proof.
       intros S1 S2 W Hsub Hunif H1 v Hv.
       destruct (seed_monotone S1 S2 v Hsub) as [Hrest Hwfrom].
       eapply Nat.le_trans; [apply Hrest|].
       eapply Nat.le_trans; [apply H1; exact Hv|].
       assert (Hinc : W + @w_from V dec allV w g S1 v + tau v <= W + @w_from V dec allV w g S2 v + tau v) by lia.
       exact Hinc.
     Qed.

     Corollary per_node_exact_sizing :
       (forall v, v <> g -> @hub_weight V w g v = (@rest_weight V dec allV w g v - tau v)) ->
       (forall s v, @next_heaven_tau V dec allV w g tau s v = Glory).
     Proof.
       intro Heq.
       apply (proj2 (@HeavenHell.heaven_one_step_all_G_iff_domination_ge_tau
                      V dec allV Hnodup Hcomplete w g tau)).
       intros v Hv.
       rewrite (Heq v Hv).
       apply HeavenHell.sub_le_to_le_add_nat.
       apply Nat.le_refl.
     Qed.

   End S.
End Monotonicity.
  
Module Async_WithTau.
    Section S.
      Import HeavenHell.

      Variable V : Type.
      Variable dec : forall x y:V, {x=y}+{x<>y}.
      Variable allV : list V.
      Hypothesis Hnodup : NoDup allV.
      Hypothesis Hcomplete : forall v:V, In v allV.
      Variable w : V -> V -> nat.
      Variable g : V.
      Variable tau : V -> nat.

      Definition async_update_tau (s:V->State) (v:V) : V->State :=
        fun u => if dec u v then @next_heaven_tau V dec allV w g tau s v else s u.

      Definition run_sched_tau (s:V->State) (sched:list V) : V->State :=
        fold_left async_update_tau sched s.

      Lemma async_update_tau_at :
        forall s v, async_update_tau s v v = @next_heaven_tau V dec allV w g tau s v.
      Proof.
        intros s v. unfold async_update_tau.
        destruct (dec v v) as [_|C]; [reflexivity|contradiction].
      Qed.

      Lemma async_update_tau_other :
        forall s v u, u <> v -> async_update_tau s v u = s u.
      Proof.
        intros s v u Huv. unfold async_update_tau.
        destruct (dec u v) as [E|NE]; [congruence|reflexivity].
      Qed.

      Lemma unchanged_if_not_in_tau :
        forall sched s v, ~ In v sched -> run_sched_tau s sched v = s v.
      Proof.
        induction sched as [|a tl IH]; intros s v Hnin.
        - cbn. reflexivity.
        - cbn [run_sched_tau fold_left].
          assert (Hneq : v <> a) by (intro E; apply Hnin; left; symmetry; exact E).
          assert (Hnintl : ~ In v tl) by (intro Hin; apply Hnin; right; exact Hin).
          change (fold_left async_update_tau tl (async_update_tau s a) v)
            with (run_sched_tau (async_update_tau s a) tl v).
          rewrite IH by exact Hnintl.
          now rewrite async_update_tau_other by exact Hneq.
      Qed.

      Lemma in_sched_makes_Glory_tau :
        forall sched s v,
          In v sched ->
          (forall s v, @next_heaven_tau V dec allV w g tau s v = Glory) ->
          run_sched_tau s sched v = Glory.
      Proof.
        induction sched as [|a tl IH]; intros s v Hin Hall.
        - contradiction.
        - cbn [run_sched_tau fold_left].
          destruct Hin as [Hv | Hin_tl].
          + set (s' := async_update_tau s a).
            assert (Hseta : s' a = Glory).
            { subst s'. rewrite async_update_tau_at. apply Hall. }
            change (fold_left async_update_tau tl s' v)
              with (run_sched_tau s' tl v).
            destruct (in_dec dec v tl) as [Hin' | Hnin'].
            * apply IH; assumption.
            * rewrite (unchanged_if_not_in_tau tl s' v Hnin').
              rewrite <- Hv. exact Hseta.
          + change (fold_left async_update_tau tl (async_update_tau s a) v)
              with (run_sched_tau (async_update_tau s a) tl v).
            apply IH; assumption.
      Qed.

      Theorem async_one_pass_all_G_nonhub_tau :
        (forall v, v <> g -> @hub_weight V w g v + tau v >= @rest_weight V dec allV w g v) ->
        forall sched s, (forall v, v <> g -> In v sched) ->
        forall v, v <> g -> run_sched_tau s sched v = Glory.
      Proof.
        intros Hdom sched s Hcover v Hv.
        pose proof (proj2 (@heaven_one_step_all_G_iff_domination_ge_tau
                            V dec allV Hnodup Hcomplete w g tau)) as Hiff.
        specialize (Hiff Hdom).
        apply in_sched_makes_Glory_tau; [apply Hcover; exact Hv | exact Hiff].
      Qed.

    End S.
  End Async_WithTau.

  Module Counterexample_Tau.
    Section S.
      Import HeavenHell.

      Variable V : Type.
      Variable dec : forall x y:V, {x=y}+{x<>y}.
      Variable allV : list V.
      Hypothesis Hnodup : NoDup allV.
      Hypothesis Hcomplete : forall v:V, In v allV.
      Variable w : V -> V -> nat.
      Variable g : V.
      Variable tau : V -> nat.
      Variable W : nat.
      Hypothesis hub_uniform : forall v, v <> g -> @hub_weight V w g v = W.

      Theorem uniform_hub_tau_below_threshold_counterexample :
        W < @max_need_tau V dec allV w g tau ->
        exists v, v <> g /\ ((@next_heaven_tau V dec allV w g tau (@all_glory V) v = Glory -> False)
                  \/ @next_heaven_tau V dec allV w g tau (@all_gnash V) v = Gnash).
      Proof.
        intro Hlt.
        pose proof (@HeavenHell.uniform_hub_tau_below_threshold_counterexample
                      V dec allV Hnodup Hcomplete w g W hub_uniform tau Hlt)
          as Hex.
        destruct Hex as [v [Hv Hgn]].
        exists v; split; [exact Hv|]. right; exact Hgn.
      Qed.

    End S.
  End Counterexample_Tau.

  Module Compute.
    Section S.
      Import HeavenHell.

      Variable V : Type.
      Variable dec : forall x y:V, {x=y}+{x<>y}.
      Variable allV : list V.
      Hypothesis Hnodup : NoDup allV.
      Hypothesis Hcomplete : forall v:V, In v allV.
      Variable w : V -> V -> nat.
      Variable g : V.
      Variable tau : V -> nat.

      Definition nonhubs : list V := HeavenHell.nonhubs dec allV g.

      Definition rest_weight_compute (v:V) : nat :=
        @sum_all V allV (fun u => if dec u g then 0 else w u v).

      Lemma rest_weight_compute_correct v :
        rest_weight_compute v = @rest_weight V dec allV w g v.
      Proof. reflexivity. Qed.

      Definition max_rest_compute : nat :=
        list_max (map rest_weight_compute nonhubs).

      Lemma max_rest_compute_correct :
        max_rest_compute = @max_rest V dec allV w g.
      Proof.
        unfold max_rest_compute, max_rest, nonhubs.
        erewrite map_ext_in with (l:=HeavenHell.nonhubs dec allV g).
        - reflexivity.
        - intros v Hv. apply rest_weight_compute_correct.
      Qed.

      Definition need_tau_compute (v:V) : nat :=
        rest_weight_compute v - tau v.

      Lemma need_tau_compute_correct v :
        need_tau_compute v = @need_tau V dec allV w g tau v.
      Proof. unfold need_tau_compute, need_tau; now rewrite rest_weight_compute_correct. Qed.

      Definition max_need_tau_compute : nat :=
        list_max (map need_tau_compute nonhubs).

      Lemma max_need_tau_compute_correct :
        max_need_tau_compute = @max_need_tau V dec allV w g tau.
      Proof.
        unfold max_need_tau_compute, max_need_tau, nonhubs.
        erewrite map_ext_in with (l:=HeavenHell.nonhubs dec allV g).
        - reflexivity.
        - intros v Hv. apply need_tau_compute_correct.
      Qed.

      Corollary uniform_hub_one_step_from_max_rest_compute :
        forall (W:nat), (forall v, v <> g -> @hub_weight V w g v = W) ->
        W >= max_rest_compute ->
        forall s v, @next_heaven V dec allV w g s v = Glory.
      Proof.
        intros W Hunif HW.
        rewrite max_rest_compute_correct in HW.
        apply (proj2 (@uniform_hub_one_step_iff V dec allV Hnodup Hcomplete w g W Hunif)).
        exact HW.
      Qed.

      Corollary uniform_hub_tau_one_step_from_max_need_compute :
        forall (W:nat), (forall v, v <> g -> @hub_weight V w g v = W) ->
        W >= max_need_tau_compute ->
        forall s v, @next_heaven_tau V dec allV w g tau s v = Glory.
      Proof.
        intros W Hunif HW.
        rewrite max_need_tau_compute_correct in HW.
        apply (proj2 (@uniform_hub_tau_one_step_iff V dec allV Hnodup Hcomplete w g W Hunif tau)).
        exact HW.
      Qed.

    End S.
  End Compute.

Module ConservationMajority.
  Section S.
    Import HeavenHell.

    Variable V : Type.
    Variable dec : forall x y:V, {x=y}+{x<>y}.
    Variable allV : list V.
    Hypothesis Hnodup : NoDup allV.
    Hypothesis Hcomplete : forall v:V, In v allV.
    Variable w : V -> V -> nat.
    Variable g : V.
    Variable tau : V -> nat.

    (* Partition of the two-state indicator *)
    Lemma ind_state_partition : forall y:State,
      ind (state_eqb y Glory) + ind (state_eqb y Gnash) = 1.
    Proof. intro y; destruct y; cbn [state_eqb ind]; lia. Qed.

    Definition total_in (v:V) : nat :=
      @sum_all V allV (fun u => w u v).

    (* Conservation: score_G + score_N equals total inbound weight *)
    Lemma score_conservation :
      forall s v,
        @score V allV w (@force_g V dec g s) Glory v
      + @score V allV w (@force_g V dec g s) Gnash v
      = total_in v.
    Proof.
      intros s v.
      unfold total_in, score.
      rewrite <- (@sum_all_add V allV
                   (fun u => w u v * ind (state_eqb (@force_g V dec g s u) Glory))
                   (fun u => w u v * ind (state_eqb (@force_g V dec g s u) Gnash))).
      apply (@sum_all_ext V allV); intros u _.
      rewrite <- Nat.mul_add_distr_l, ind_state_partition; lia.
      Qed.

    (* Majority-form characterization with tau (ties -> Glory) *)
    Lemma next_heaven_tau_majority_form :
      forall s v,
        v <> g ->
        (@next_heaven_tau V dec allV w g tau s v = Glory
         <-> 2 * @score V allV w (@force_g V dec g s) Glory v + tau v
             >= total_in v).
    Proof.
      intros s v Hvg.
      set (SG := @score V allV w (@force_g V dec g s) Glory v).
      set (SN := @score V allV w (@force_g V dec g s) Gnash v).
      pose proof (@score_conservation s v) as Hcons; cbv zeta in Hcons.
      pose proof (@next_heaven_tau_eq_Glory_iff_not_g
                    V dec allV w g tau s v Hvg) as Hiff.
      (* Hiff: next=Glory <-> SN <= SG + tau v *)
      split.
      - intro HG.
        apply Hiff in HG.
        (* HG: SN <= SG + tau v *)
        (* Want: 2*SG + tau v >= total_in v *)
        rewrite <- Hcons.
        lia.
      - intro Hmaj.
        (* Hmaj: 2*SG + tau v >= total_in v *)
        rewrite <- Hcons in Hmaj.
        (* Now: 2*SG + tau v >= SG + SN  ==> SN <= SG + tau v *)
        apply Hiff.
        lia.
      Qed.

    (* A convenience restatement for the uniform-hub threshold, in majority form. *)
    Corollary uniform_threshold_majority :
      forall (W:nat),
        (forall v, v <> g -> @hub_weight V w g v = W) ->
        (forall s v, @next_heaven_tau V dec allV w g tau s v = Glory)
        <-> (forall v, v <> g ->
              2 * @hub_weight V w g v + tau v >= total_in v).
    Proof.
      intros W Hunif.
      rewrite (@uniform_hub_tau_one_step_iff V dec allV Hnodup Hcomplete w g W Hunif tau).
      split.
      - (* W >= max_need_tau -> per-node inequality in majority form *)
        intros HW v Hv.
        (* From global bound, get per-node need bound *)
        pose proof ((proj1 (@max_need_tau_le_iff V dec allV Hcomplete w g tau W) HW) v Hv) as Hneed.
        unfold total_in.
        (* total_in = hub_weight v + rest_weight v *)
        pose proof (@total_weight_split V dec allV Hnodup Hcomplete w g v) as Hsplit.
        rewrite Hsplit.
        rewrite (Hunif v Hv).
        (* Using Hneed: rest - tau <= W  <->  2W + tau >= W + rest *)
        lia.
      - (* per-node majority inequality -> W >= max_need_tau *)
        intro Hmaj.
        apply (proj2 (@max_need_tau_le_iff V dec allV Hcomplete w g tau W)).
        intros v Hv.
        pose proof (Hmaj v Hv) as Hnode.
        pose proof (@total_weight_split V dec allV Hnodup Hcomplete w g v) as Hsplit.
        unfold total_in in Hnode.
        rewrite Hsplit in Hnode.
        rewrite (Hunif v Hv) in Hnode.
        lia.
    Qed.

  End S.
End ConservationMajority.
